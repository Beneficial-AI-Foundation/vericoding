// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

spec fn positive(s: Seq<int>) -> bool {
    forall|u: int|0<=u<s.len() ==> s[u]>=0
}
spec fn isEven(i: int)
requires i>=0
{i%2==0}


// ATOM 

function CountEven(s:seq<int>):int
requires positive(s) -> bool {
    if s==[] then 0
 else (if (s[s.len()-1]%2==0) then 1 else 0)+CountEven(s[..s.len()-1])
}

fn mcountEven(v: Vec<int>) -> (n: int)
    requires positive(v[..])
    ensures n==CountEven(v[..])
{
}

}