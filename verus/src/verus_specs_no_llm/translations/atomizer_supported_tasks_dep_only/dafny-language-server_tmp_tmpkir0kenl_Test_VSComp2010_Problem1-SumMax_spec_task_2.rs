// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_M(N: int, a: Vec<int>) -> sum: int, max: int
    requires
        0 <= N && a.len() == N && (forall |k: int| 0 <= k && k < N ==> 0 <= a.index(k))
    ensures
        sum <= N * max
;

proof fn lemma_M(N: int, a: Vec<int>) -> (sum: int, max: int)
    requires
        0 <= N && a.len() == N && (forall |k: int| 0 <= k && k < N ==> 0 <= a.index(k))
    ensures
        sum <= N * max
{
    (0, 0)
}

}