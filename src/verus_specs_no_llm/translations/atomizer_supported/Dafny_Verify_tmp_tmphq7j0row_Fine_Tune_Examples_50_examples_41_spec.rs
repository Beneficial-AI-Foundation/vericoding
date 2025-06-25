// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn main(n: int, k: int) -> i: int, j: int
    requires n >= 0,
             k == 1 or k >= 0
    ensures k + i + j >= 2 * n
{
}

}