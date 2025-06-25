// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn add_small_numbers(a: Vec<int>, n: int, max: int) -> (r: int)
    requires n > 0;,
             n <= a.len();,
             (forall i: int :: 0 <= i and i < n ==> a[i] <= max);
    ensures r <= max * n;
{
}

}