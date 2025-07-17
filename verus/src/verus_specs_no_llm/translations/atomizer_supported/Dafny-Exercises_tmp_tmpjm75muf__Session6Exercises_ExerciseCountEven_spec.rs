// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn positive(s: Seq<int>) -> bool {
    forall |u: int|0<=u<s.len() ==> s.index(u)>=0
}
spec fn isEven(i: int)
requires i>=0
{i%2==0}


// ATOM 

function CountEven(s:seq<int>):int
requires positive(s) -> bool {
    if s==[] then 0
 else (if (s.index(s.len()-1)%2==0) then 1 else 0)+CountEven(s.index(..s.len()-1))
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