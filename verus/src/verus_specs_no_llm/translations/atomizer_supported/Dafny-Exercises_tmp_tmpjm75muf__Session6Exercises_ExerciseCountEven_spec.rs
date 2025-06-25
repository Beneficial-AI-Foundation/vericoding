// Translated from Dafny
use builtin::*;
use builtin_macros::*;

use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn positive(s: Seq<int>) -> bool {
    forall u::0<=u<s.len() ==> s.spec_index(u)>=0
}
spec fn isEven(i: int)
requires i>=0
{i%2==0}


// ATOM 

function CountEven(s:seq<int>):int
requires positive(s) -> bool {
    if s==[] then 0
 else (if (s.spec_index(s.len()-1)%2==0) then 1 else 0)+CountEven(s.spec_index(..s.len()-1))
}

fn mcountEven(v: Vec<int>) -> (n: int)
    requires
        positive(v.spec_index(..))
    ensures
        n==CountEven(v.spec_index(..))
{
    return 0;
}

}