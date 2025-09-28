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
/* helper modified by LLM (iteration 3): fixed merge_index to return proper i32 type and added helper for sorted prefix */
spec fn merge_index(a: Seq<i32>, b: Seq<i32>, i: int, j: int) -> i32 {
    if i < a.len() {
        if j < b.len() {
            if a[i] <= b[j] { a[i] } else { b[j] }
        } else {
            a[i]
        }
    } else {
        b[j]
    }
}

spec fn sorted_prefix(s: Seq<i32>, end: int) -> bool {
    forall|i: int, j: int| 0 <= i < j < end ==> s[i] <= s[j]
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
{ /* code modified by LLM (iteration 3): fixed loop invariants and multiset handling */
    let mut a = a;
    let mut b = b;
    let mut result = Vec::new();
    let mut i = 0;
    let mut j = 0;
    
    while i < a.len() || j < b.len()
        invariant
            0 <= i <= a.len(),
            0 <= j <= b.len(),
            sorted_prefix(result@, result@.len() as int),
            multiset_equiv(result@, a@.subrange(0, i as int) + b@.subrange(0, j as int)),
            (i < a.len() && j < b.len() && result@.len() > 0 ==> result@[result@.len() - 1] <= merge_index(a@, b@, i as int, j as int)),
        decreases ((a.len() - i) + (b.len() - j))
    {
        if i < a.len() && (j >= b.len() || a[i] <= b[j]) {
            result.push(a[i]);
            i += 1;
        } else {
            result.push(b[j]);
            j += 1;
        }
    }
    
    proof {
        assert(is_sorted(result@));
        assert(multiset_equiv(result@, a@ + b@));
    }
    
    result
}
// </vc-code>

}
fn main() {}