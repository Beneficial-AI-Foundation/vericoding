// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn ComputeAvg(a: int, b: int) -> (avg: int)
    ensures
        avg == (a+b)/2
{
    return 0;
}

}