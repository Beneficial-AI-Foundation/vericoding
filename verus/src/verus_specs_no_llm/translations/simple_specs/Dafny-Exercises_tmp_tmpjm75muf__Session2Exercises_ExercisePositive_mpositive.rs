// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn positive(s: Seq<int>) -> bool {
    forall |u: int|0<=u<s.len() ==> s.index(u)>=0
}

spec fn spec_mpositive(v: Vec<int>) -> b:bool
    ensures
        b==positive(v.index(0..v.len()))
;

proof fn lemma_mpositive(v: Vec<int>) -> (b: bool)
    ensures
        b==positive(v.index(0..v.len()))
{
    false
}

}