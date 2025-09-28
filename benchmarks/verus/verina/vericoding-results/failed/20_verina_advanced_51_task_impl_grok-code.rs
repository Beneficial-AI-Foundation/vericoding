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
/* code modified by LLM (iteration 4): implementing merge of two sorted vectors with corrected invariants for inner loops to ensure invariants hold and final assertions pass */
    let mut i = 0;
    let mut j = 0;
    let mut result = Vec::new();
    while i < a.len() && j < b.len()
        invariant
            0 <= i <= a.len(),
            0 <= j <= b.len(),
            result.len() == i + j,
            forall |k: int| 0 <= k < i ==> a@[k] == result@[k],
            forall |k: int| 0 <= k < j ==> b@[k] == result@[i + k],
            is_sorted(result@),
        decreases (a.len() - i) + (b.len() - j)
    {
        if a[i] <= b[j] {
            result.push(a[i]);
            i += 1;
        } else {
            result.push(b[j]);
            j += 1;
        }
    }
    if i < a.len() {
        let mut k = i;
        while k < a.len()
            invariant
                i <= k <= a.len(),
                result.len() == i + j + (k - i),
                forall |m: int| 0 <= m < k ==> result@[m] == a@[m],
                forall |m: int| 0 <= m < j ==> result@[i + m] == b@[m],
                is_sorted(result@),
            decreases a.len() - k
        {
            result.push(a[k]);
            k += 1;
        }
    } else if j < b.len() {
        let mut k = j;
        while k < b.len()
            invariant
                j <= k <= b.len(),
                result.len() == i + k,
                forall |m: int| 0 <= m < i ==> result@[m] == a@[m],
                forall |m: int| 0 <= m < k ==> result@[i + m] == b@[m],
                is_sorted(result@),
            decreases b.len() - k
        {
            result.push(b[k]);
            k += 1;
        }
    }
    proof {
        assert(multiset_equiv(result@, a@ + b@));
        assert(is_sorted(result@));
    }
    result
}
// </vc-code>

}
fn main() {}