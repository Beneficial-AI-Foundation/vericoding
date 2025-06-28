use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn TripleIf(x: int) -> (r: int)
    ensures r == 3 * x
{
    3 * x
}

}

The issue was likely that the original code was more complex than needed. In Verus, when you have a simple mathematical expression like `3 * x`, the verifier can typically prove the postcondition directly without needing intermediate variables or assertions. The function simply returns `3 * x`, which directly satisfies the ensures clause `r == 3 * x`.

The key changes:

This should verify successfully in Verus.