// Translated from Dafny
#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

#[allow(unused_imports)]
use builtin::*;
#[allow(unused_imports)]
use builtin_macros::*;

verus! {

fn main() {
}

fn Search(s: Seq<int>, x: int) -> (k: int )
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
        forall p,q  0 <= p < q < .len()s| :: s.spec_index(p) <= s.spec_index(q);
    ensures
        0 <= k <= s.len();,
        forall i | 0 <= i < k :: s.spec_index(i) <= x;,
        forall i  k <= i < .len()s| :: s.spec_index(i) >= x;,
        forall z | z in s.spec_index(..k) :: z <= x;,
        forall z | z in s.spec_index(k..) :: z >= x;,
        s == s.spec_index(..k)+s.spec_index(k..);,
        multiset(r) == m;,
        forall p,q  0 <= p < q < .len()r| :: r.spec_index(p) <= r.spec_index(q);
{
    return (0, 0);
}

}