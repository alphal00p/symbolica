//! Variable real arguments for the existing bounded GPL suffix engine.
//!
//! Ordinary GPL convention: every letter has kernel `1/(t-a)`. The supported
//! alphabet is `{-1,0,1}`, weight at most six, along `0 <= x <= 1`. No complex
//! continuation is performed. All input coordinates are exact rationals.
//!
//! At x<=1/2 the existing fixed-point recurrence is used with multiplier x/a.
//! Trailing zeros use the existing shuffle expansion. For larger x, Chen
//! composition gives G(w;1-y)=sum_k G(1-w[..k];y) P(w[k..]), with tangential
//! endpoint constants P determined by this same identity at one half. Every
//! numerical operation retains an outward error enclosure. At x=1 convergent
//! regular words call the existing endpoint-one GPL evaluator directly.

use super::*;
use crate::domains::float::FloatLike;

/// A batch of real GPLs sharing native fixed-point and ball arithmetic.
///
/// Up to 4096 words of weight six are accepted. Each evaluation is bounded by
/// 250 million suffix-series updates and at most one million working bits.
/// Unsupported endpoints and exhausted budgets return errors, never samples.
/// At x=1, the empty word is one and nonempty all-zero words are zero;
/// other supported words must start with a letter other than one and end
/// with a nonzero letter. Finite exceptional words outside that endpoint
/// class, such as G(1,0;1), are rejected explicitly.
pub struct RealGplEvaluator {
    words: Vec<Vec<i8>>,
    periods: Mutex<BTreeMap<(Vec<i8>, u32), RealBall>>,
}

impl RealGplEvaluator {
    pub fn new(words: &[Vec<i8>]) -> Result<Self, String> {
        if words.len() > MAX_WORDS {
            return Err("real GPL batch exceeds 4096 words".into());
        }
        for word in words {
            validate_word(word)?;
        }
        Ok(Self {
            words: words.to_vec(),
            periods: Mutex::new(BTreeMap::new()),
        })
    }

    /// One working-precision pass, retaining complete absolute error radii.
    /// Small arguments or cancellation can leave fewer reliable bits than the
    /// working precision. Use `evaluate` for a requested output accuracy.
    pub fn evaluate_balls(&self, x: &Rational, bits: u32) -> Result<Vec<RealBall>, String> {
        check_coordinate(x, bits)?;
        let mut budget = Budget(MAX_SERIES_WORK);
        self.evaluate_with_budget(x, bits, &mut budget)
    }

    fn evaluate_with_budget(
        &self,
        x: &Rational,
        bits: u32,
        budget: &mut Budget,
    ) -> Result<Vec<RealBall>, String> {
        check_coordinate(x, bits)?;
        self.words
            .iter()
            .map(|word| self.at(word, x, bits, budget))
            .collect()
    }

    /// Evaluate with at least `bits` reliable bits for every nonzero result,
    /// retaining bounds after final rounding. Exact zero remains exact zero.
    /// Guard precision increases for the complete batch when required.
    pub fn evaluate(&self, x: &Rational, bits: u32) -> Result<Vec<RealBall>, String> {
        check_coordinate(x, bits)?;
        let weight = self.words.iter().map(Vec::len).max().unwrap_or(0) as u64;
        let mut loss = if x.is_zero() {
            0
        } else {
            x.denominator_ref()
                .significant_bits()
                .saturating_sub(x.numerator_ref().significant_bits())
        };
        if x != &Rational::one()
            && self
                .words
                .iter()
                .any(|word| !word.is_empty() && word.iter().all(|&a| a == 0))
        {
            let complement = Rational::one() - x;
            loss = loss.max(
                complement
                    .denominator_ref()
                    .significant_bits()
                    .saturating_sub(complement.numerator_ref().significant_bits()),
            );
        }
        let mut guard = 64u64.saturating_add(weight.saturating_mul(loss));
        let mut budget = Budget(MAX_SERIES_WORK);
        for _ in 0..8 {
            let work = u64::from(bits)
                .checked_add(guard)
                .filter(|p| *p <= u64::from(MAX_BITS))
                .ok_or("real GPL requested accuracy exceeds the working-precision ceiling")?
                as u32;
            let balls = self.evaluate_with_budget(x, work, &mut budget)?;
            let mut rounded = Vec::with_capacity(balls.len());
            let mut success = true;
            for ball in balls {
                let tracked = TrackedComplex::from_ball(
                    Complex::new(ball, RealBall::exact(Float::new(work))),
                    ErrorQuality::Bounded,
                );
                match tracked.rounded(Some(bits)) {
                    Ok(value)
                        if value.precision().real.exact_zero
                            || value
                                .precision()
                                .real
                                .significant_bits
                                .is_some_and(|p| p >= bits)
                                && value.ball.re.center.get_precision() >= bits =>
                    {
                        rounded.push(value.ball.re)
                    }
                    _ => {
                        success = false;
                        break;
                    }
                }
            }
            if success {
                return Ok(rounded);
            }
            guard = guard.saturating_mul(2);
        }
        Err("real GPL could not enclose the requested accuracy after guard retries".into())
    }

    /// Enclose an uncertain real coordinate for words regular at zero.
    /// Their derivatives have fixed sign `(-1)^(number of one letters)` on
    /// (0,1), by induction through the defining integrals. Therefore evaluating
    /// both exact rational endpoints encloses the complete input interval.
    /// Trailing-zero words are excluded from this monotonicity contract.
    pub fn evaluate_interval(&self, x: &RealBall, bits: u32) -> Result<Vec<RealBall>, String> {
        if !x.is_finite()
            || x.radius < x.radius.zero()
            || self.words.iter().any(|w| w.last() == Some(&0))
        {
            return Err(
                "real GPL interval evaluation needs a finite input and no trailing zeros".into(),
            );
        }
        let center = x.center.to_rational();
        let radius = x.radius.to_rational();
        let lower = &center - &radius;
        let upper = &center + &radius;
        let mut budget = Budget(MAX_SERIES_WORK);
        let left = self.evaluate_with_budget(&lower, bits, &mut budget)?;
        let right = if lower == upper {
            left.clone()
        } else {
            self.evaluate_with_budget(&upper, bits, &mut budget)?
        };
        Ok(left
            .into_iter()
            .zip(right)
            .zip(&self.words)
            .map(|((a, b), word)| {
                let (low, high) = if word.iter().filter(|&&a| a == 1).count() % 2 == 0 {
                    (a, b)
                } else {
                    (b, a)
                };
                RealBall::from_rational_bounds(
                    &(low.center.to_rational() - low.radius.to_rational()),
                    &(high.center.to_rational() + high.radius.to_rational()),
                    bits,
                )
            })
            .collect())
    }

    fn at(
        &self,
        word: &[i8],
        x: &Rational,
        bits: u32,
        budget: &mut Budget,
    ) -> Result<RealBall, String> {
        if word.is_empty() {
            return Ok(exact_integer(1, bits));
        }
        if x.is_zero() {
            return if word.iter().all(|&a| a == 0) {
                Err("all-zero GPL diverges at zero".into())
            } else {
                Ok(exact_integer(0, bits))
            };
        }
        if x == &Rational::one() {
            if word.iter().all(|&a| a == 0) {
                return Ok(exact_integer(0, bits));
            }
            let letters = word
                .iter()
                .map(|a| match a {
                    -1 => GplLetter::MinusOne,
                    0 => GplLetter::Zero,
                    1 => GplLetter::One,
                    _ => unreachable!(),
                })
                .collect::<Vec<_>>();
            // Conservative graph-size bound for the existing endpoint graph.
            budget.consume(
                (word.len() * (word.len() + 1)) as u64 * u64::from(series_terms(word.len(), bits)),
            )?;
            return EndpointOneGplEvaluator::new(&letters)?
                .evaluate_ball(bits)
                .map(|v| v.re);
        }
        if x <= &Rational::from((1, 2)) {
            return direct(&[word.to_vec()], x, bits, budget).map(|mut v| v.remove(0));
        }
        let y = Rational::one() - x;
        let reflected = word.iter().map(|a| 1 - a).collect::<Vec<_>>();
        let mut value = self.period(word, bits, budget)?;
        for split in 1..=word.len() {
            let suffix = self.period(&word[split..], bits, budget)?;
            if suffix.is_zero() {
                continue;
            }
            let prefix = direct(&[reflected[..split].to_vec()], &y, bits, budget)?.remove(0);
            value += prefix * suffix;
        }
        Ok(value)
    }

    fn period(&self, word: &[i8], bits: u32, budget: &mut Budget) -> Result<RealBall, String> {
        if word.is_empty() {
            return Ok(exact_integer(1, bits));
        }
        if word.iter().all(|&a| a == 0) || word.iter().all(|&a| a == 1) {
            return Ok(exact_integer(0, bits));
        }
        let key = (word.to_vec(), bits);
        if let Some(value) = self
            .periods
            .lock()
            .map_err(|_| "real GPL cache poisoned")?
            .get(&key)
        {
            return Ok(value.clone());
        }
        let half = Rational::from((1, 2));
        let mut value = direct(&[word.to_vec()], &half, bits, budget)?.remove(0);
        let reflected = word.iter().map(|a| 1 - a).collect::<Vec<_>>();
        for split in 1..=word.len() {
            let suffix = self.period(&word[split..], bits, budget)?;
            if suffix.is_zero() {
                continue;
            }
            let prefix = direct(&[reflected[..split].to_vec()], &half, bits, budget)?.remove(0);
            value -= prefix * suffix;
        }
        let mut cache = self.periods.lock().map_err(|_| "real GPL cache poisoned")?;
        if cache.len() >= MAX_WORDS
            || cache.keys().map(|(_, p)| u64::from(*p)).sum::<u64>() + u64::from(bits) > 64_000_000
        {
            cache.clear();
        }
        cache.insert(key, value.clone());
        Ok(value)
    }
}

fn check_coordinate(x: &Rational, bits: u32) -> Result<(), String> {
    if !(2..=MAX_BITS).contains(&bits) || x < &Rational::zero() || x > &Rational::one() {
        Err("real GPL needs 0 <= x <= 1 and 2..=1000000 working bits".into())
    } else {
        Ok(())
    }
}

fn exact_integer(value: i64, bits: u32) -> RealBall {
    RealBall::exact(Float::with_val(bits, value))
}

struct Budget(u64);
impl Budget {
    fn consume(&mut self, work: u64) -> Result<(), String> {
        self.0 = self
            .0
            .checked_sub(work)
            .ok_or("real GPL series work limit exceeded")?;
        Ok(())
    }
}

/// The same suffix graph, fixed-point recurrence, and proof as the sixth-root
/// evaluator. Only the exact kernel multiplier differs: x/a instead of 1/(2a).
fn direct(
    words: &[Vec<i8>],
    x: &Rational,
    bits: u32,
    budget: &mut Budget,
) -> Result<Vec<RealBall>, String> {
    debug_assert!(!x.is_zero() && x <= &Rational::from((1, 2)));
    let mut memo = BTreeMap::new();
    let expansions = words
        .iter()
        .map(|word| remove_trailing_zeros(word, &mut memo))
        .collect::<Vec<_>>();
    let regular = expansions
        .iter()
        .flat_map(|e| e.keys().map(|(word, _)| word.clone()))
        .collect::<BTreeSet<_>>();
    let mut nodes = Vec::new();
    let mut indices = BTreeMap::from([(Vec::new(), 0)]);
    for word in regular {
        intern_poles(&word, &mut nodes, &mut indices);
    }
    let weight = nodes.iter().map(|n| n.weight).max().unwrap_or(1);
    budget.consume(nodes.len() as u64 * u64::from(series_terms(weight, bits)))?;
    let numerator = x.numerator_ref();
    let denominator = x.denominator_ref();
    let (fixed, terms) = evaluate_fixed_nodes(
        &nodes,
        bits,
        |a| *a == 0,
        |a, value| {
            // Every internal nonzero letter is -1,1,or2. Thus |x/a|<=1/2;
            // exact integer division rounds each component toward zero by <1 ulp.
            let divisor = denominator * i64::from(*a);
            Fixed {
                a: (value.a * numerator) / &divisor,
                b: (value.b * numerator) / divisor,
            }
        },
    )?;
    let scale = Integer::one() << bits;
    let values = fixed
        .into_iter()
        .enumerate()
        .map(|(index, value)| {
            debug_assert!(value.b.is_zero());
            RealBall::from_rational_ball(
                &Rational::from((value.a, scale.clone())),
                &Rational::from((
                    Integer::from(fixed_error(&nodes, index, terms)),
                    scale.clone(),
                )),
                bits,
            )
        })
        .collect::<Vec<_>>();
    let log = RealBall::from_rational_ball(x, &Rational::zero(), bits).log();
    let mut logs = vec![exact_integer(1, bits)];
    for power in 1..=MAX_WEIGHT {
        logs.push(&logs[power - 1] * &log);
    }
    Ok(expansions
        .into_iter()
        .map(|expansion| {
            let mut result = exact_integer(0, bits);
            for ((word, power), coefficient) in expansion {
                let coefficient =
                    RealBall::from_rational_ball(&coefficient, &Rational::zero(), bits);
                result += &values[indices[&word]] * &logs[power] * coefficient;
            }
            result
        })
        .collect())
}

#[cfg(test)]
mod tests;
