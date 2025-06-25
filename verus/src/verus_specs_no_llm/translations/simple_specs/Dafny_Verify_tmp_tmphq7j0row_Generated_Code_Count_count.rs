// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

fn count(v: int, a: Vec<int>, n: int) -> (r: int)
    requires
        n >= 0 && n <= a.len()
    ensures
        has_count(v, a, n) == r
{
    return 0;
}

}