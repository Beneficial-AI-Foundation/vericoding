// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn Search(s: Seq<int>, x: int) -> k: int )
    // Ekki má breyta forskilyrðum eða eftirskilyrðum fallsins
    requires forall p, q | 0 <= p < q < |s|: : s[p] <= s[q];
    ensures 0 <= k <= |s|;
    ensures forall i | 0 <= i < k :: s[i] <= x;
    ensures forall i | k <= i < |s| :: s[i] >= x;
    ensures forall z | z in s[..k] :: z <= x;
    ensures forall z | z in s[k..] :: z >= x;
    ensures s == s[..k]+s[k..];
{
}


// SPEC 

method Sort( m: multiset<int> ) returns ( r: seq<int>
    requires forall|p: int, q  0 <= p < q < .len()s|: int| s[p] <= s[q];
    ensures 0 <= k <= s.len();,
            forall|i | 0 <= i < k: int| s[i] <= x;,
            forall|i  k <= i < .len()s|: int| s[i] >= x;,
            forall|z | z in s[..k]: int| z <= x;,
            forall|z | z in s[k..]: int| z >= x;,
            s == s[..k]+s[k..];,
            multiset(r) == m;,
            forall|p: int, q  0 <= p < q < .len()r|: int| r[p] <= r[q];
{
}

}