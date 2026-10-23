//! Bounded angle form of the same Jonquiere expansion used by the ordinary
//! integer-polylogarithm evaluator (DLMF 25.12.9, 25.12.12 and 25.6.2).

use super::*;

const MAX_BITS: u32 = 1_000_000;

/// Evaluate the real generalized Clausen functions with a complete enclosure.
///
/// Supported orders are `2`, meaning `Im Li_2(exp(i theta))`, and `3`, meaning
/// `Re Li_3(exp(i theta))`. The entire real angle enclosure must lie strictly
/// inside `(-2*pi, 2*pi)`. Negative angles use odd/even parity respectively;
/// intervals containing zero use the continuous limiting values. A numerical
/// angle near pi is never rounded to the exact mathematical endpoint.
///
/// The result includes source uncertainty, every arithmetic rounding error,
/// and a proven geometric tail bound. The input's error quality is preserved:
/// an estimated input does not become certified by evaluating this function.
/// Evaluation uses exactly `bits` working bits, without hidden escalation.
/// The supported range is `2..=1_000_000`; a fixed budget of `4*bits+64` series
/// terms prevents unbounded work near `2*pi`. Exhaustion returns an error,
/// never a partial sum. Very low precision may fail to resolve a finite bound;
/// this also returns an error. Nontrivial bounds require `float-mpfr`.
///
/// This is a native numerical API; no extra symbolic function or separate
/// ordinary point evaluator is introduced. Other integer orders, periodic
/// range reduction, and complex angles require further bounded continuation.
pub fn clausen_tracked(
    order: u32,
    angle: &TrackedComplex,
    bits: u32,
) -> Result<TrackedComplex, String> {
    if !(2..=MAX_BITS).contains(&bits) {
        return Err("tracked Clausen working precision is outside 2..=1000000 bits".into());
    }
    validate(angle, bits)?;
    if !matches!(order, 2 | 3) {
        return Err("tracked Clausen currently supports orders two and three".into());
    }
    if !is_real(&angle.ball) {
        return Err("tracked Clausen requires an entirely real angle enclosure".into());
    }
    if real_zero(&angle.ball.re) {
        return Ok(real(
            if order == 2 {
                point(0, bits)
            } else {
                zeta_integer_bound(3, bits)?
            },
            angle.error_quality,
        ));
    }
    let mut input = angle.ball.re.clone();
    input.set_precision(bits);
    let lower = input.lower_bound();
    let upper = input.upper_bound();
    let zero = Float::new(bits);
    let pi = constant(Symbol::PI, bits)?.ball.re;
    let two_pi_lower = (point(2, bits) * pi.clone()).lower_bound();
    let largest = if -lower.clone() > upper {
        -lower.clone()
    } else {
        upper.clone()
    };
    if largest >= two_pi_lower {
        return Err("tracked Clausen angle enclosure must be provably inside (-2*pi,2*pi)".into());
    }
    let value = if lower >= zero {
        nonnegative(order, input, &pi, bits)?
    } else if upper <= zero {
        let positive = nonnegative(order, -input, &pi, bits)?;
        if order == 2 { -positive } else { positive }
    } else if order == 3 {
        // Even parity maps the whole source interval onto [0,max(abs ends)].
        nonnegative(order, RealBall::from_bounds(zero, largest), &pi, bits)?
    } else {
        let positive = nonnegative(order, RealBall::from_bounds(zero.clone(), upper), &pi, bits)?;
        let negative = -nonnegative(order, RealBall::from_bounds(zero, -lower), &pi, bits)?;
        hull(&positive, &negative)
    };
    checked(Complex::new(value, point(0, bits)), angle.error_quality)
}

fn hull(first: &RealBall, second: &RealBall) -> RealBall {
    let a = first.lower_bound();
    let b = second.lower_bound();
    let c = first.upper_bound();
    let d = second.upper_bound();
    RealBall::from_bounds(if a < b { a } else { b }, if c > d { c } else { d })
}

fn leading_point(order: u32, x: &Float, bits: u32) -> Result<RealBall, String> {
    if x.is_fully_zero() {
        return Ok(point(0, bits));
    }
    let log = directed_unary(Unary::Log, x, bits)?;
    let x = RealBall::exact(x.clone());
    Ok(if order == 2 {
        x * (point(1, bits) - log)
    } else {
        x.pow(2) / point(2, bits) * (log - point(3, bits) / point(2, bits))
    })
}

/// The removable zero endpoint cannot be evaluated as zero times log(zero).
/// Bound the continuous leading term using its endpoint values and its sole
/// interior extremum: maximum 1 at x=1 for order two, minimum -e^2/4 at x=e
/// for order three. The rest of each series has nonnegative coefficients.
fn nonnegative(order: u32, x: RealBall, pi: &RealBall, bits: u32) -> Result<RealBall, String> {
    // Reconstruct a nonnegative enclosure explicitly: the ball's midpoint
    // representation can otherwise widen a mathematical zero endpoint below
    // zero by one rounding unit. Clamping here retains the proved input domain.
    let lower = x.lower_bound();
    let upper = x.upper_bound();
    let zero = Float::new(bits);
    let lower = if lower < zero { zero.clone() } else { lower };
    if upper.is_fully_zero() {
        return if order == 2 {
            Ok(point(0, bits))
        } else {
            zeta_integer_bound(3, bits)
        };
    }
    let mut sum = hull(
        &leading_point(order, &lower, bits)?,
        &leading_point(order, &upper, bits)?,
    );
    // Compute extrema against the actual nonnegative endpoints; do not pass
    // the subsequently re-centered ball through log at a spurious negative.
    if order == 2 {
        let one = Float::with_val(bits, 1);
        if lower <= one && upper >= one {
            sum = hull(&sum, &point(1, bits));
        }
    } else {
        let e = constant(Symbol::E, bits)?.ball.re;
        if lower <= e.upper_bound() && upper >= e.lower_bound() {
            sum = hull(&sum, &(-e.pow(2) / point(4, bits)));
        }
        sum += zeta_integer_bound(3, bits)?;
    }
    let x = RealBall::from_bounds(lower, upper.clone());
    let q = square(&(x.clone() / (point(2, bits) * pi.clone())), bits);
    let q_upper = q.upper_bound();
    if q_upper >= Float::with_val(bits, 1) {
        return Err(
            "tracked Clausen precision cannot resolve its geometric convergence gap".into(),
        );
    }
    let r = RealBall::exact(q_upper);
    let gap = point(1, bits) - r.clone();
    let mut power = q.clone();
    let mut bound_power = r.clone();
    // Cl2 tends to zero as theta*log(theta). An absolute-only threshold loses
    // relative accuracy for small angles even when the source has ample bits.
    // Scaling by min(1,upper) keeps the tail below its natural small-angle
    // scale; C3 tends to zeta(3) and needs no such scaling.
    let tolerance_scale = if order == 2 && upper < Float::with_val(bits, 1) {
        upper.clone()
    } else {
        Float::with_val(bits, 1)
    };
    let tolerance = Float::with_val(bits, 0.5).pow(u64::from(bits) + 8) * tolerance_scale;
    let max_terms = bits * 4 + 64;
    let u = RealBall::exact(upper);
    for n in 1..=max_terms {
        // DLMF 25.6.2 turns Bernoulli/factorial coefficients into bounded
        // positive even-zeta values. This is the ordinary dilog Jonquiere
        // recurrence, without constructing growing exact Bernoulli numbers.
        let coefficient = zeta_integer_bound(2 * n, bits)?;
        let denominator = Rational::from(n) * Rational::from(2 * n + 1);
        let denominator = if order == 3 {
            denominator * Rational::from(2 * n + 2)
        } else {
            denominator
        };
        let denominator = RealBall::from_rational_bounds(&denominator, &denominator, bits);
        let term = coefficient * power.clone() * if order == 2 { x.clone() } else { x.pow(2) }
            / denominator;
        if order == 2 {
            sum += term;
        } else {
            sum -= term;
        }

        // For n>=1, 1<zeta(2n)<2, and successive positive terms decrease
        // by a factor below q. The entire remaining tail after n is bounded
        // by 2*u*q^(n+1)/[(n+1)(2n+3)(1-q)], with a further u/(2n+4)
        // for order three. All majorant arithmetic is outward rounded.
        bound_power *= r.clone();
        let denominator = Rational::from(n + 1) * Rational::from(2 * n + 3);
        let denominator = if order == 3 {
            denominator * Rational::from(2 * n + 4)
        } else {
            denominator
        };
        let denominator = RealBall::from_rational_bounds(&denominator, &denominator, bits);
        let bound =
            (point(2, bits) * bound_power.clone() * if order == 2 { u.clone() } else { u.pow(2) }
                / (denominator * gap.clone()))
            .upper_bound();
        if !bound.is_finite() {
            return Err("tracked Clausen tail bound is not finite".into());
        }
        if bound <= tolerance {
            // The positive-angle tail has a known sign. Keep that information
            // instead of assigning an arbitrary symmetric truncation error.
            let tail = RealBall::from_bounds(zero, bound);
            return Ok(if order == 2 { sum + tail } else { sum - tail });
        }
        power *= q.clone();
    }
    Err("tracked Clausen exhausted its fixed-precision term budget".into())
}

#[cfg(test)]
mod tests;
