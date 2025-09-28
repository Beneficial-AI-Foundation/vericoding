// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix recursive multiplication spec and lemmas with proper decreases */
proof fn multiply_spec_lemma(a: int, b: int) -> (result: int)
    ensures result == a * b,
{
    if b >= 0 {
        lemma_multiply_nonnegative(a, b);
    } else {
        lemma_multiply_negative(a, b);
    }
    a * b
}

proof fn lemma_multiply_nonnegative(a: int, b: int)
    requires b >= 0,
    ensures a * b == multiply_recursive(a, b),
    decreases b,
{
    reveal_with_fuel(multiply_recursive, 3);
    if b > 0 {
        lemma_multiply_nonnegative(a, b - 1);
        assert(multiply_recursive(a, b) == a + multiply_recursive(a, b - 1));
        assert(a * b == a + (a * (b - 1)));
    }
}

proof fn lemma_multiply_negative(a: int, b: int)
    requires b < 0,
    ensures a * b == multiply_recursive(a, b),
    decreases -b,
{
    reveal_with_fuel(multiply_recursive, 3);
    lemma_multiply_nonnegative(a, -b);
    assert(multiply_recursive(a, b) == -a + multiply_recursive(a, b + 1));
    assert(a * b == -a + (a * (b + 1)));
}

spec fn multiply_recursive(a: int, b: int) -> int
    decreases if b >= 0 { b } else { -b },
{
    if b == 0 {
        0
    } else if b > 0 {
        a + multiply_recursive(a, b - 1)
    } else {
        -a + multiply_recursive(a, b + 1)
    }
}
// </vc-helpers>

// <vc-spec>
fn multiply(a: i32, b: i32) -> (result: i32)
    ensures result == a * b,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fix while loop with proper arithmetic and invariants */
{
    let mut result: i32 = 0;
    let mut counter: i32 = b;
    
    while counter != 0
        invariant
            result == (b - counter) * a,
        decreases if counter > 0 { counter as int } else { (-counter) as int },
    {
        if counter > 0 {
            result = result + a;
            counter = counter - 1;
        } else {
            result = result - a;
            counter = counter + 1;
        }
    }
    
    proof {
        multiply_spec_lemma(a as int, b as int);
    }
    result
}
// </vc-code>

}
fn main() {}