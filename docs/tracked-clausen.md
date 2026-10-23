# Tracked Clausen evaluation

`symbolica::transcendental::clausen_tracked(order, &angle, working_bits)`
provides a native enclosure for the real functions

```text
order 2: Im Li_2(exp(i theta)) = sum(k >= 1) sin(k theta)/k^2
order 3: Re Li_3(exp(i theta)) = sum(k >= 1) cos(k theta)/k^3
```

The supported class comprises orders two and three and entirely real input
intervals provably contained in `(-2*pi, 2*pi)`. The first function is odd and
the second is even. Input intervals may contain zero. A numerical argument
near pi retains its uncertainty; it is never replaced by an exact endpoint.
The result's imaginary component is structurally zero, and the input's
`ErrorQuality` is preserved.

Nontrivial enclosures use the MPFR backend's directed pi, logarithm and integer
zeta primitives. Unsupported backends, orders, complex angles, invalid radii,
and intervals outside the declared domain return errors. Arbitrary working
precision is selected at runtime, from 2 through 1,000,000 bits. Evaluation
uses the requested precision throughout; it does not silently retry or invent
an accuracy certificate from the bit count. A budget of `4*working_bits+64`
terms bounds work. Near the convergence boundary this budget can be exhausted;
very low precision can also fail to resolve a finite outward bound. The
error does not contain a partial successful result. Periodic range
reduction and further orders require additional bounded continuation.

## Shared algorithm and tail

This extends the existing integer-polylogarithm Jonquiere evaluator to tracked
angle inputs. It reuses the same recurrence and the shared directed integer
`zeta_u` helper instead of recomputing large Bernoulli numbers. For positive
`theta`, with `q=(theta/(2*pi))^2`, its series are

```text
C2 = theta*(1-log(theta))
     + sum(n >= 1) zeta(2n)*theta*q^n/[n*(2n+1)]
C3 = zeta(3) + theta^2/2*(log(theta)-3/2)
     - sum(n >= 1) zeta(2n)*theta^2*q^n/[n*(2n+1)*(2n+2)]
```

These follow from the [Clausen integral](https://dlmf.nist.gov/25.12.E9),
[Jonquiere expansion](https://dlmf.nist.gov/25.12.E12), and
[Bernoulli–zeta relation](https://dlmf.nist.gov/25.6.E2). Both positive-term
sequences have successive ratios smaller than `q`. For an angle interval with
upper endpoint `u`, outward rounding supplies a bound `r >= (u/(2*pi))^2`.
Using `zeta(2n)<2`, the tails after term `N` are bounded by

```text
R2 <= 2*u*r^(N+1)/[(N+1)*(2N+3)*(1-r)]
R3 <= R2*u/(2N+4).
```

The known tail sign is retained. The result includes both this truncation
bound and all interval arithmetic and input uncertainty. Ordinary floating
transcendental calls without error models are not used.
The stopping threshold is `2^(-working_bits-8)`, scaled by `min(1,u)` for
order two to retain relative accuracy as the angle tends to zero. This is a
tail budget, not a promise that source uncertainty or cancellation permits
the same relative accuracy in the returned enclosure.

At zero the two logarithmic leading terms have continuous limits zero. Their
interval ranges use their endpoint values and any interior extremum: maximum
one at `theta=1` for the order-two leading term, and minimum `-e^2/4` at
`theta=e` for the order-three leading term. This avoids evaluating `0*log(0)`
and avoids an incorrect assumption of monotonicity. Negative and crossing-zero
intervals use parity and interval unions.

## Independent fixtures

`src/transcendental/tracked/clausen/mathematica.tsv` contains ten diagnostic
fixtures from Mathematica 15.0.1: `PolyLog` evaluated at 500-digit angle inputs,
460-digit intermediate precision and 400-digit real/imaginary projections,
exported to 340 digits. The exact rational angles are `1/10`, `1`, `3`, `5`
and `10^-20`, for both orders. Mathematica is not a runtime or test dependency.
The tests also use independent special values at zero, pi/2 and pi, test
uncertain intervals across turning points and zero, and exercise nonstandard
requested bit widths, tiny angles, malformed inputs and resource exhaustion.

Validation with the MPFR backend covers all ten independent fixtures at 53,
113, 137, 256, 512 and 1024 bits. All 18 selected tracked-transcendental tests
and nine tracked-expression regression tests pass; the existing slow
20,000-digit polylogarithm acceptance test remains ignored. The Astro backend
passes both input-validation and explicit unsupported-bound tests. These
tests use `--no-default-features` with `integer-gmp,serde,native_code_generation`
and exactly one of `float-mpfr` or `float-astro`. The native-code feature is
needed by existing unrelated unit-test code; Clausen evaluation does not
generate or compile source.
