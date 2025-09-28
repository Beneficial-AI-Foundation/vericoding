use vstd::prelude::*;

verus! {

// <vc-helpers>
proof fn lemma_divides(numerator: int, denominator: int, divisor: int)
    requires 0 < denominator,
        0 < divisor,
        numerator % (denominator * divisor) == 0
    ensures (numerator / denominator) % divisor == numerator / (denominator * divisor)
{
    assert(numerator == denominator * (numerator / denominator));
    assert(numerator % (denominator * divisor) == 0);
    let q = numerator / (denominator * divisor);
    assert(denominator * divisor * q == numerator);
    assert(denominator * (numerator / denominator) == numerator);
    assert(denominator * divisor * q == denominator * (numerator / denominator));
    assert(divisor * q == numerator / denominator);
    assert((numerator / denominator) % divisor == 0);
    assert((numerator / denominator) / divisor == q);
}

proof fn lemma_division_by_multiplication(a: int, b: int, c: int)
    requires 0 < c,
        (a * b) % c == 0
    ensures (a * b) / c == a * (b / c) + (a % c) * (b / c) + a * (b % c) / c
{
    assert(a * b == (a / c) * c * b + (a % c) * b);
    assert((a * b) % c == ((a % c) * b) % c);
}

proof fn lemma_degrees_to_radians(degrees: int)
    ensures
        (degrees * pi_approx()) / scale_factor() / 180 == (degrees * pi_approx()) / (scale_factor() * 180)
{
    lemma_divides(degrees * pi_approx(), scale_factor(), 180);
}
// </vc-helpers>

// <vc-spec>
spec fn pi_approx() -> int { 314159265358979323846i128 as int }
spec fn scale_factor() -> int { 100000000000000000000i128 as int }

fn degrees_to_radians(degrees: i64) -> (radians: i64)
    ensures radians as int == (degrees as int * pi_approx()) / scale_factor() / 180
// </vc-spec>
// <vc-code>
{
    let degrees_int = degrees as int;
    let product = degrees_int * pi_approx();
    lemma_degrees_to_radians(degrees_int);
    let scaled = product / scale_factor() / 180;
    scaled as i64
}
// </vc-code>

fn main() {
}

}