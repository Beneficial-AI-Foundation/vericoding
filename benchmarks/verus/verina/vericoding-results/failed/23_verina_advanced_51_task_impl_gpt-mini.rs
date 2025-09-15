// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_sorted(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] <= s[j]
}

spec fn multiset_equiv(s1: Seq<i32>, s2: Seq<i32>) -> bool {
    s1.to_multiset() == s2.to_multiset()
}
// </vc-preamble>

// <vc-helpers>
spec fn merge_spec(sa: Seq<i32>, sb: Seq<i32>) -> Seq<i32> {
    if sa.len() == 0 {
        sb
    } else if sb.len() == 0 {
        sa
    } else {
        if sa[0] <= sb[0] {
            seq![sa[0]] + merge_spec(sa[1..], sb)
        } else {
            seq![sb[0]] + merge_spec(sa, sb[1..])
        }
    }
}

proof fn merge_spec_preserves_sorted(sa: Seq<i32>, sb: Seq<i32>)
    requires is_sorted(sa) && is_sorted(sb)
    ensures is_sorted(merge_spec(sa, sb))
{
}

proof fn merge_spec_multiset_equiv(sa: Seq<i32>, sb: Seq<i32>)
    ensures merge_spec(sa, sb).to_multiset() == (sa + sb).to_multiset()
{
}

proof fn merge_spec_length(sa: Seq<i32>, sb: Seq<i32>)
    ensures merge_spec(sa, sb).len() == sa.len() + sb.len()
{
}

// </vc-helpers>

// <vc-spec>
fn merge_sorted(a: Vec<i32>, b: Vec<i32>) -> (result: Vec<i32>)
    requires 
        is_sorted(a@),
        is_sorted(b@),
    ensures 
        is_sorted(result@),
        multiset_equiv(result@, a@ + b@),
// </vc-spec>
// <vc-code>
{
    let m = merge_spec(a@, b@);
    let total: int = m.len();
    let mut res: Vec<i32> = Vec::new();
    let mut k: int = 0;
    while k < total
        invariant 0 <= k <= total
        invariant res@ == m[..k]
        decreases total - k
    {
        res.push(m[k]);
        k += 1;
    }
    proof {
        merge_spec_preserves_sorted(a@, b@);
        merge_spec_multiset_equiv(a@, b@);
    }
    res
}

// </vc-code>

}
fn main() {}