// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn max(a: Vec<int>, n: int) -> (max: int)
    requires 0 < n <= a.len();
    ensures is_max(max, a, n);
{
}

}