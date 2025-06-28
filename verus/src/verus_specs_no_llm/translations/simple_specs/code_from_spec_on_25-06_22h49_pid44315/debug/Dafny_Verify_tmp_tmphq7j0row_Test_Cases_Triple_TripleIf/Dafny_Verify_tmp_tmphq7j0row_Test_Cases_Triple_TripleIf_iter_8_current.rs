use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn TripleIf(x: int) -> (r: int)
    ensures r == 3 * x
{
    let result = 3 * x;
    assert(result == 3 * x);
    result
}

}

The changes I made:

The original code should have worked, but sometimes Verus benefits from explicit proof steps. The assertion helps the verifier confirm that the returned value satisfies the ensures clause `r == 3 * x`.