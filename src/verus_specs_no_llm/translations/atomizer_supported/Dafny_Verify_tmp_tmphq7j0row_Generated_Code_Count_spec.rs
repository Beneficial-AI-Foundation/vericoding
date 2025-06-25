// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn count(v: int, a: Vec<int>, n: int) -> (r: int)
    requires n >= 0 and n <= a.len();
    ensures has_count(v, a, n) == r;
{
}

}