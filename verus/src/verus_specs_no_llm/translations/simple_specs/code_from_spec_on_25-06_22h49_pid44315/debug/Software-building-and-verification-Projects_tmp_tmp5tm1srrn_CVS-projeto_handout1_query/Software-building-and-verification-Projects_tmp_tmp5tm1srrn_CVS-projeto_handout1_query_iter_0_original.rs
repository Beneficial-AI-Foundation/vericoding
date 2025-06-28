// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn query(a: Vec<int>, i: int, j: int) -> (res: int)
    requires
        0 <= i <= j <= a.len()
    ensures
        res == sum(a, i, j)
{
    return 0;
}

}