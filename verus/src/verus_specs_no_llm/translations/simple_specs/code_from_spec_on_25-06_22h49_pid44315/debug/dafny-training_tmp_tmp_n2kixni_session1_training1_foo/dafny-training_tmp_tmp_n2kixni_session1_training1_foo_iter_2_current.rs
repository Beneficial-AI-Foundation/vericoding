use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn abs(x: int) -> (y: int)
    ensures y >= 0 && (x >= 0 ==> y == x) && (x < 0 ==> y == -x)
{
    if x >= 0 {
        x
    } else {
        -x
    }
}

fn foo(x: int) -> (result: int)
    requires x >= 0
    ensures result >= 0
{
    let result = abs(x);
    assert(x >= 0);
    assert(result >= 0 && (x >= 0 ==> result == x) && (x < 0 ==> result == -x));
    assert(x >= 0 ==> result == x);
    assert(result == x);
    assert(result >= 0);
    result
}

}

The key changes I made:

   - Asserting the precondition `x >= 0`
   - Asserting the postcondition of `abs(x)`
   - Using the implication to conclude `result == x`
   - Finally asserting that `result >= 0` (since `x >= 0` and `result == x`)

This should help Verus verify that when `x >= 0`, calling `abs(x)` returns `x` itself, which is non-negative, thus satisfying the postcondition `result >= 0`.