// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_Cubes(n: int) -> s:seq<int>
    requires
        n >= 0
    ensures
        s.len() == n,
        forall |i: int| 0 <= i < n ==> s.index(i) == i*i*i
;

proof fn lemma_Cubes(n: int) -> (s: Seq<int>)
    requires
        n >= 0
    ensures
        s.len() == n,
        forall |i: int| 0 <= i < n ==> s.index(i) == i*i*i
{
    Seq::empty()
}

}