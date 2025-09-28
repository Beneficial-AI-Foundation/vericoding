// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(h: int, a: int) -> bool {
    h >= 1 && a >= 1
}

spec fn is_minimum_attacks(attacks: int, h: int, a: int) -> bool {
    attacks >= 1 &&
    attacks * a >= h &&
    (attacks - 1) * a < h
}

spec fn ceil_div(h: int, a: int) -> int
    recommends a > 0
{
    (h + a - 1) / a
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_ceil_div_bounds(h: int, a: int)
    requires
        valid_input(h, a),
    ensures
        1 <= ceil_div(h, a),
        ceil_div(h, a) <= h,
{
    let k = ceil_div(h, a);
    assert(a >= 1);
    assert(h >= 1);

    // Lower bound: ceil_div(h, a) >= 1 because h + a - 1 >= a
    assert(a <= h + a - 1);
    assert(1 <= k);

    // Upper bound: ceil_div(h, a) <= h because a*h >= h + a - 1 when h >= 1 and a >= 1
    assert(a - 1 >= 0);
    assert(h - 1 >= 0);
    assert((a - 1) * (h - 1) >= 0);
    assert(a * h - h - a + 1 >= 0);
    assert(a * h >= h + a - 1);
    assert(k <= h);
}

proof fn lemma_ceil_div_min_attacks(h: int, a: int)
    requires
        valid_input(h, a),
    ensures
        is_minimum_attacks(ceil_div(h, a), h, a),
{
    let k = ceil_div(h, a);
    lemma_ceil_div_bounds(h, a);

    // Show k * a >= h
    assert(h + a - 1 < (k + 1) * a);
    assert(h <= k * a);

    // Show (k - 1) * a < h
    assert(k * a <= h + a - 1);
    assert((k - 1) * a <= h - 1);
    assert((k - 1) * a < h);
}

// </vc-helpers>

// <vc-spec>
fn solve(h: i8, a: i8) -> (attacks: i8)
    requires 
        valid_input(h as int, a as int)
    ensures 
        is_minimum_attacks(attacks as int, h as int, a as int),
        attacks as int == ceil_div(h as int, a as int)
// </vc-spec>
// <vc-code>
{
    let hi: int = h as int;
    let ai: int = a as int;

    proof {
        lemma_ceil_div_bounds(hi, ai);
        lemma_ceil_div_min_attacks(hi, ai);
    }

    let k: int = ceil_div(hi, ai);

    // Prove bounds to allow safe cast to i8
    assert(1 <= k);
    assert(k <= hi);

    let attacks: i8 = k as i8;

    assert(attacks as int == k);

    attacks
}
// </vc-code>


}

fn main() {}