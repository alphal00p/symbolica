use super::*;
use crate::atom::AtomCore;
use crate::parse;
use std::collections::HashMap;

fn rational(numerator: i64, denominator: i64) -> Rational {
    Rational::from((numerator, denominator))
}

#[test]
fn real_gpl_matches_all_eight_independent_330_digit_integrals() {
    let data = include_str!("mathematica.tsv");
    let rows = data
        .lines()
        .filter(|line| !line.starts_with('#') && !line.is_empty())
        .collect::<Vec<_>>();
    assert_eq!(rows.len(), 8);
    let evaluator = RealGplEvaluator::new(&[vec![-1, 0, 0, 1], vec![0, 1, 0, 1]]).unwrap();
    for bits in [113, 173, 256, 512, 1024] {
        let mut keys = BTreeSet::new();
        for row in &rows {
            let fields = row.split('\t').collect::<Vec<_>>();
            assert_eq!(fields.len(), 3);
            assert!(keys.insert((fields[0], fields[1])));
            let x = match fields[1] {
                "1/2" => rational(1, 2),
                "9/10" => rational(9, 10),
                "1" => Rational::one(),
                "1/100000000000000000000" => {
                    Rational::from((Integer::one(), Integer::from(10).pow(20)))
                }
                _ => panic!("unknown fixture argument"),
            };
            let index = match fields[0] {
                "minus_one_zero_zero_one" => 0,
                "zero_one_zero_one" => 1,
                _ => panic!("unknown fixture basis"),
            };
            let result = evaluator.evaluate(&x, bits).unwrap().remove(index);
            let reference = Float::parse(fields[2], Some(1200)).unwrap();
            // The 330-digit source uncertainty is much smaller than every
            // retained ball here; include it explicitly in the comparison.
            let uncertainty = reference.norm() * Float::parse("1e-329", Some(1200)).unwrap();
            assert!(
                (result.center.to_rational() - reference.to_rational()).abs()
                    <= result.radius.to_rational() + uncertainty.to_rational(),
                "{bits} bits: {row}, ball={result:?}"
            );
        }
        assert_eq!(keys.len(), 8);
    }
}

#[test]
fn arbitrary_words_shuffle_trailing_zeros_and_native_polylogs() {
    let words = [
        vec![-1],
        vec![0, 1],
        vec![-1, 0, 1],
        vec![0, -1, 1],
        vec![0, 1, -1],
        vec![1, 0],
        vec![0],
        vec![1],
        vec![-1, -1, -1],
    ];
    let evaluator = RealGplEvaluator::new(&words).unwrap();
    for x in [rational(1, 3), rational(1, 2), rational(9, 10)] {
        let v = evaluator.evaluate(&x, 173).unwrap();
        assert!((&v[0] * &v[1]).intersects(&(&v[2] + &v[3] + &v[4])));
        assert!((&v[5] + &v[1]).intersects(&(&v[6] * &v[7])));
        assert!(v[8].intersects(&(v[0].pow(3) / exact_integer(6, 173))));
        let input = Float::new(256).from_rational(&x);
        let expected: Float = -parse!("polylog(2,x)")
            .evaluate_with_prec(&HashMap::from([(parse!("x"), input)]), 256)
            .unwrap();
        assert!(v[1].contains(&expected));
    }
}

#[test]
fn both_sides_of_the_half_point_match_native_classical_values() {
    let evaluator = RealGplEvaluator::new(&[vec![-1], vec![0, 1]]).unwrap();
    let half = rational(1, 2);
    let delta = Rational::from((Integer::one(), Integer::one() << 200u32));
    let mut values = Vec::new();
    for x in [&half - &delta, half.clone(), &half + &delta] {
        let evaluated = evaluator.evaluate(&x, 512).unwrap();
        let input = Float::new(768).from_rational(&x);
        let log = (input.clone() + 1).log();
        let li: Float = parse!("polylog(2,x)")
            .evaluate_with_prec(&HashMap::from([(parse!("x"), input)]), 768)
            .unwrap();
        assert!(evaluated[0].contains(&log));
        assert!(evaluated[1].contains(&(-li)));
        values.push(evaluated);
    }
    assert!(values[0][0].upper_bound() < values[1][0].lower_bound());
    assert!(values[1][0].upper_bound() < values[2][0].lower_bound());
    assert!(
        RealGplEvaluator::new(&[vec![0, 0, 0]])
            .unwrap()
            .evaluate(&Rational::one(), 173)
            .unwrap()[0]
            .is_zero()
    );
}

#[test]
fn sub_binary64_endpoint_distances_and_tiny_values_remain_distinct() {
    let evaluator = RealGplEvaluator::new(&[vec![-1, 0, 0, 1], vec![0, 1, 0, 1]]).unwrap();
    let delta = Rational::from((Integer::one(), Integer::one() << 200u32));
    let near = evaluator
        .evaluate(&(Rational::one() - &delta), 512)
        .unwrap();
    let end = evaluator.evaluate(&Rational::one(), 512).unwrap();
    assert!(near[0].lower_bound() > end[0].upper_bound());
    assert!(near[1].upper_bound() < end[1].lower_bound());
    let tiny = Rational::from((Integer::one(), Integer::from(10).pow(200)));
    for value in evaluator.evaluate(&tiny, 173).unwrap() {
        assert!(value.is_strictly_positive() || value.is_strictly_negative());
        assert!(value.center.norm() < Float::parse("1e-399", Some(173)).unwrap());
    }
    let endpoint_distance = Rational::from((Integer::one(), Integer::one() << 2000u32));
    let logarithm = RealGplEvaluator::new(&[vec![0]])
        .unwrap()
        .evaluate(&(Rational::one() - &endpoint_distance), 113)
        .unwrap()
        .remove(0);
    assert!(logarithm.is_strictly_negative());
    let leading = -Float::new(256).from_rational(&endpoint_distance);
    assert!(logarithm.contains(&leading));
}

#[test]
fn input_intervals_preserve_their_uncertainty_and_domain() {
    let evaluator = RealGplEvaluator::new(&[vec![-1, 0, 0, 1], vec![0, 1, 0, 1]]).unwrap();
    let malformed = RealBall {
        center: Float::with_val(256, 0.5),
        radius: Float::with_val(256, -0.1),
    };
    assert!(evaluator.evaluate_interval(&malformed, 256).is_err());
    let input = RealBall::from_rational_bounds(&rational(8, 10), &rational(9, 10), 256);
    let interval = evaluator.evaluate_interval(&input, 256).unwrap();
    for x in [rational(8, 10), rational(17, 20), rational(9, 10)] {
        let point = evaluator.evaluate(&x, 384).unwrap();
        for (a, b) in interval.iter().zip(point) {
            assert!(a.contains_ball(&b));
        }
    }
    assert!(
        evaluator
            .evaluate_interval(
                &RealBall::new(Float::new(256), Float::with_val(256, 1)),
                256
            )
            .is_err()
    );
    assert!(
        RealGplEvaluator::new(&[vec![0]])
            .unwrap()
            .evaluate_interval(&input, 256)
            .is_err()
    );
    assert!(RealGplEvaluator::new(&[vec![2]]).is_err());
    assert!(RealGplEvaluator::new(&[vec![0; 7]]).is_err());
    assert!(
        RealGplEvaluator::new(&[vec![1]])
            .unwrap()
            .evaluate(&Rational::one(), 173)
            .is_err()
    );
    assert!(
        RealGplEvaluator::new(&[vec![0]])
            .unwrap()
            .evaluate(&Rational::zero(), 173)
            .is_err()
    );
    assert!(evaluator.evaluate(&rational(3, 2), 173).is_err());
}
