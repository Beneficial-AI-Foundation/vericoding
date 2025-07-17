// Translated from Dafny
use builtin::*;
use builtin_macros::*;

verus! {

fn main() {
}

spec fn spec_Search(s: Seq<int>, x: int) -> k: int )
    // Ekki má breyta forskilyrðum eða eftirskilyrðum fallsins
    requires forall p,q | 0 <= p < q < |s| :: s[p] <= s[q];
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
    requires
        forall p,q  0 <= p < q < .len()s| :: s.index(p) <= s.index(q)
    ensures
        0 <= k <= s.len(),
        forall i | 0 <= i < k :: s.index(i) <= x,
        forall i  k <= i < .len()s| :: s.index(i) >= x,
        forall z | z in s.index(..k) :: z <= x,
        forall z | z in s.index(k..) :: z >= x,
        s == s.index(..k)+s.index(k..),
        multiset(r) == m,
        forall p,q  0 <= p < q < .len()r| :: r.index(p) <= r.index(q)
;

proof fn lemma_Search(s: Seq<int>, x: int) -> (k: int )
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

method Sort( m: multiset<int> ) returns ( r: seq<int>)
    requires
        forall p,q  0 <= p < q < .len()s| :: s.index(p) <= s.index(q)
    ensures
        0 <= k <= s.len(),
        forall i | 0 <= i < k :: s.index(i) <= x,
        forall i  k <= i < .len()s| :: s.index(i) >= x,
        forall z | z in s.index(..k) :: z <= x,
        forall z | z in s.index(k..) :: z >= x,
        s == s.index(..k)+s.index(k..),
        multiset(r) == m,
        forall p,q  0 <= p < q < .len()r| :: r.index(p) <= r.index(q)
{
    (0, 0)
}

}