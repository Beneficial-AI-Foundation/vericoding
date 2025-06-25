// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn M(N: int, a: Vec<int>) -> sum: int, max: int
    requires 0 <= N and a.len() == N and (forall|k: int| 0 <= k and k < N ==> 0 <= a[k]);
    ensures sum <= N * max;
{
}

}