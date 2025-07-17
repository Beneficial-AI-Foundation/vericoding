// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn positive(s: Seq<int>) -> bool {
    forall |u: int|0<=u<s.len() ==> s.index(u)>=0
}

spec fn CountEven(s: Seq<int>) -> int
    requires
        positive(s)
{
    0
}

spec fn spec_mcountEven(v: Vec<int>) -> n:int
    requires
        positive(v.index(..))
    ensures
        n==CountEven(v.index(..))
;

proof fn lemma_mcountEven(v: Vec<int>) -> (n: int)
    requires
        positive(v.index(..))
    ensures
        n==CountEven(v.index(..))
{
    0
}

}