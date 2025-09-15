// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
fn mul_recursive(a: int, b: int) -> int
    decreases if b < 0 { -b } else { b }
{
    if b == 0 {
        0
    } else if b > 0 {
        a + mul_recursive(a, b - 1)
    } else {
        mul_recursive(a, b + 1) - a
    }
}

proof fn lemma_mul_is_mul_recursive(a: int, b: int)
    ensures mul_recursive(a, b) == a * b
    decreases if b < 0 { -b } else { b }
{
    if b == 0 {
        // Trivial
    } else if b > 0 {
        lemma_mul_is_mul_recursive(a, b - 1);
    } else {
        lemma_mul_is_mul_recursive(a, b + 1);
    }
}
// </vc-helpers>

// <vc-spec>
fn multiply(a: i32, b: i32) -> (result: i32)
    ensures result == a * b,
// </vc-spec>
// <vc-code>
{
    proof {
        lemma_mul_is_mul_recursive(a as int, b as int);
    }
    let result = (a as int * b as int) as i32;
    result
}
// </vc-code>

}
fn main() {}