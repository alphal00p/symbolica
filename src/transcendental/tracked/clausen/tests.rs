use super::*;

fn exact(value: Rational, bits: u32) -> TrackedComplex {
    real(
        RealBall::from_rational_bounds(&value, &value, bits),
        ErrorQuality::Bounded,
    )
}

#[cfg(feature = "float-mpfr")]
fn interval(lower: Rational, upper: Rational, bits: u32) -> TrackedComplex {
    real(
        RealBall::from_rational_bounds(&lower, &upper, bits),
        ErrorQuality::Bounded,
    )
}

#[cfg(feature = "float-mpfr")]
fn ordinary_reference(order: u32, angle: &Float, bits: u32) -> Float {
    let mut angle = angle.clone();
    angle.set_precision(bits);
    let arg = Complex::new(Float::new(bits), angle).exp();
    let order_arg = Complex::new(Float::with_val(bits, order), Float::new(bits));
    let result = crate::transcendental::polylog_numeric_eval(&order_arg, &arg, bits).unwrap();
    if order == 2 { result.im } else { result.re }
}

#[cfg(feature = "float-mpfr")]
#[test]
fn independent_mathematica_values_converge_at_arbitrary_runtime_widths() {
    let rows = include_str!("mathematica.tsv")
        .lines()
        .filter(|line| !line.starts_with('#') && !line.is_empty())
        .collect::<Vec<_>>();
    assert_eq!(rows.len(), 10);
    for bits in [53, 113, 137, 256, 512, 1024] {
        let mut seen = std::collections::BTreeSet::new();
        for row in &rows {
            let fields = row.split('\t').collect::<Vec<_>>();
            assert_eq!(fields.len(), 3);
            let order: u32 = fields[0].parse().unwrap();
            assert!(seen.insert((order, fields[1])));
            assert_eq!(
                fields[2]
                    .split('e')
                    .next()
                    .unwrap()
                    .chars()
                    .filter(char::is_ascii_digit)
                    .count(),
                340,
                "independent fixture must retain all exported digits"
            );
            let argument = match fields[1] {
                "1/10" => Rational::from((1, 10)),
                "1" => Rational::one(),
                "3" => Rational::from(3),
                "5" => Rational::from(5),
                "1/100000000000000000000" => {
                    Rational::from((Integer::one(), Integer::from(10).pow(20)))
                }
                _ => panic!("unregistered exact fixture argument"),
            };
            let result = clausen_tracked(order, &exact(argument, bits), bits).unwrap();
            let reference = Float::parse(fields[2], Some(1200)).unwrap();
            let source_error = reference.norm() * Float::parse("1e-339", Some(1200)).unwrap();
            let distance = (result.ball.re.center.to_rational() - reference.to_rational()).abs();
            assert!(
                distance + source_error.to_rational() <= result.ball.re.radius.to_rational(),
                "{bits} bits, order {order}, x={}, ball={:?}",
                fields[1],
                result.ball.re
            );
            let allowance = reference.norm() * Float::with_val(1200, 0.5).pow(u64::from(bits - 20));
            assert!(
                result.ball.re.radius.to_rational() < allowance.to_rational(),
                "enclosure did not converge: {bits}, {row}"
            );
            assert_eq!(result.working_precision(), bits);
            assert_eq!(result.error_quality, ErrorQuality::Bounded);
            assert!(real_zero(&result.ball.im));
        }
        assert_eq!(seen.len(), 10);
    }
}

#[cfg(feature = "float-mpfr")]
#[test]
fn zero_half_pi_and_pi_match_independent_special_values() {
    use crate::domains::backend::float::MultiPrecisionFloat;
    use rug::float::{Constant, Round};
    for bits in [53, 113, 173, 256, 512, 1024] {
        let pi = constant(Symbol::PI, bits).unwrap().ball.re;
        let high = bits + 128;
        let zeta3 = zeta_integer_bound(3, high).unwrap();
        let catalan = RealBall::from_bounds(
            MultiPrecisionFloat::with_val_round(high, Constant::Catalan, Round::Down)
                .0
                .into(),
            MultiPrecisionFloat::with_val_round(high, Constant::Catalan, Round::Up)
                .0
                .into(),
        );
        let at_half_pi = real(pi.clone() / point(2, bits), ErrorQuality::Bounded);
        let c2 = clausen_tracked(2, &at_half_pi, bits).unwrap();
        assert!(c2.ball.re.contains_ball(&catalan));
        let c3 = clausen_tracked(3, &at_half_pi, bits).unwrap();
        let expected = -point(3, high) * zeta3.clone() / point(32, high);
        assert!(c3.ball.re.contains_ball(&expected));
        let at_pi = real(pi, ErrorQuality::Bounded);
        let c2 = clausen_tracked(2, &at_pi, bits).unwrap();
        assert!(c2.ball.re.contains(&Float::new(bits)));
        assert!(!c2.ball.re.radius.is_fully_zero());
        let c3 = clausen_tracked(3, &at_pi, bits).unwrap();
        assert!(
            c3.ball
                .re
                .contains_ball(&(-point(3, high) * zeta3.clone() / point(4, high)))
        );
        let zero = exact(Rational::zero(), bits);
        assert!(
            clausen_tracked(2, &zero, bits)
                .unwrap()
                .ball
                .is_fully_zero()
        );
        assert!(
            clausen_tracked(3, &zero, bits)
                .unwrap()
                .ball
                .re
                .contains_ball(&zeta3)
        );
    }
}

#[cfg(feature = "float-mpfr")]
#[test]
fn uncertain_intervals_include_turning_points_zero_and_negative_angles() {
    let bits = 173;
    let ranges = [
        (Rational::from((9, 10)), Rational::from((11, 10))),
        (Rational::from((27, 10)), Rational::from((28, 10))),
        (Rational::from((-1, 100)), Rational::from((1, 50))),
        (Rational::from((-11, 10)), Rational::from((-9, 10))),
        (Rational::zero(), Rational::from((1, 1000))),
    ];
    for (lower, upper) in ranges {
        let mut input = interval(lower.clone(), upper.clone(), bits);
        input.error_quality = ErrorQuality::Estimated;
        for order in [2, 3] {
            let result = clausen_tracked(order, &input, bits).unwrap();
            assert_eq!(result.error_quality, ErrorQuality::Estimated);
            for n in 0..=8 {
                let x = lower.clone() + (upper.clone() - &lower) * Rational::from((n, 8));
                let x = x.to_multi_prec_float(bits * 3);
                let expected = if x.is_fully_zero() {
                    if order == 2 {
                        Float::new(bits * 3)
                    } else {
                        zeta_integer_bound(3, bits * 3).unwrap().center
                    }
                } else {
                    ordinary_reference(order, &x, bits * 3)
                };
                assert!(
                    result.ball.re.contains(&expected),
                    "order={order}, range={lower}..{upper}, x={x}, result={:?}",
                    result.ball.re
                );
            }
        }
    }
    // This interval contains the true Cl2 maximum pi/3, not an endpoint.
    let maximum =
        constant(Symbol::PI, bits * 3).unwrap().ball.re.center / Float::with_val(bits * 3, 3);
    let expected = ordinary_reference(2, &maximum, bits * 3);
    let result = clausen_tracked(
        2,
        &interval(Rational::from((9, 10)), Rational::from((11, 10)), bits),
        bits,
    )
    .unwrap();
    assert!(result.ball.re.contains(&expected));
}

#[cfg(feature = "float-mpfr")]
#[test]
fn sub_binary64_angles_and_endpoint_distances_remain_distinct() {
    let bits = 256;
    let delta = Rational::from((Integer::one(), Integer::one() << 80_u32));
    for order in [2, 3] {
        let a = clausen_tracked(order, &exact(Rational::one(), bits), bits).unwrap();
        let b = clausen_tracked(order, &exact(Rational::one() + &delta, bits), bits).unwrap();
        assert!(!a.ball.re.intersects(&b.ball.re));
    }
    let tiny = Rational::from((Integer::one(), Integer::one() << 2000_u32));
    let positive = clausen_tracked(2, &exact(tiny.clone(), 173), 173).unwrap();
    let negative = clausen_tracked(2, &exact(-tiny, 173), 173).unwrap();
    assert!(positive.ball.re.is_strictly_positive());
    assert!(negative.ball.re.is_strictly_negative());
    assert!(positive.ball.re.intersects(&(-negative.ball.re)));
    let bits = 512;
    let pi = constant(Symbol::PI, bits).unwrap().ball.re;
    let displacement = exact(
        Rational::from((Integer::one(), Integer::one() << 200_u32)),
        bits,
    )
    .ball
    .re;
    let near_pi = real(pi - displacement, ErrorQuality::Bounded);
    assert!(
        clausen_tracked(2, &near_pi, bits)
            .unwrap()
            .ball
            .re
            .is_strictly_positive()
    );
    // A caller may retain more source bits than requested for this pass.
    // Reprecision must enclose the lost input bits, not silently discard them.
    let source = exact(Rational::one() + delta, 512);
    for order in [2, 3] {
        let result = clausen_tracked(order, &source, 53).unwrap();
        let reference = ordinary_reference(order, &source.ball.re.center, 768);
        assert!(result.ball.re.contains(&reference));
        assert_eq!(result.working_precision(), 53);
    }
}

#[test]
fn invalid_inputs_orders_and_precision_limits_fail_explicitly() {
    let bits = 128;
    let value = exact(Rational::one(), bits);
    for order in [0, 1, 4, u32::MAX] {
        assert!(
            clausen_tracked(order, &value, bits)
                .unwrap_err()
                .contains("orders")
        );
    }
    for precision in [0, 1, MAX_BITS + 1, u32::MAX] {
        assert!(
            clausen_tracked(2, &value, precision)
                .unwrap_err()
                .contains("precision")
        );
    }
    let mut malformed = value.clone();
    malformed.ball.re.radius = Float::with_val(bits, -1);
    assert!(
        clausen_tracked(2, &malformed, bits)
            .unwrap_err()
            .contains("negative")
    );
    let mut nonfinite = value.clone();
    nonfinite.ball.re.center = Float::with_val(bits, f64::INFINITY);
    assert!(
        clausen_tracked(2, &nonfinite, bits)
            .unwrap_err()
            .contains("nonfinite")
    );
    let mut complex = value;
    complex.ball.im = point(1, bits);
    assert!(
        clausen_tracked(2, &complex, bits)
            .unwrap_err()
            .contains("real angle")
    );
}

#[cfg(feature = "float-mpfr")]
#[test]
fn low_precision_and_resource_exhaustion_do_not_return_partial_sums() {
    // Extremely coarse arithmetic can lose the positive convergence gap in
    // outward ball operations. Such a pass must fail, rather than report a
    // partial sum or silently evaluate with hidden guard precision.
    assert!(
        clausen_tracked(2, &exact(Rational::one(), 2), 2)
            .unwrap_err()
            .contains("bound is not finite")
    );
    let low = clausen_tracked(2, &exact(Rational::one(), 16), 16).unwrap();
    assert!(
        low.ball
            .re
            .contains(&Float::parse("1.0139591323607685", Some(128)).unwrap())
    );
    assert_eq!(low.working_precision(), 16);
    assert!(
        clausen_tracked(2, &exact(Rational::from(7), 128), 128)
            .unwrap_err()
            .contains("inside")
    );
    assert!(
        clausen_tracked(2, &exact(Rational::from((6283, 1000)), 53), 53)
            .unwrap_err()
            .contains("term budget")
    );
}

#[cfg(not(feature = "float-mpfr"))]
#[test]
fn unsupported_backend_is_explicit_without_approximated_bounds() {
    assert!(
        clausen_tracked(2, &exact(Rational::zero(), 128), 128)
            .unwrap()
            .ball
            .is_fully_zero()
    );
    for order in [2, 3] {
        assert!(
            clausen_tracked(order, &exact(Rational::one(), 128), 128)
                .unwrap_err()
                .contains("float-mpfr")
        );
    }
    assert!(
        clausen_tracked(3, &exact(Rational::zero(), 128), 128)
            .unwrap_err()
            .contains("float-mpfr")
    );
}
