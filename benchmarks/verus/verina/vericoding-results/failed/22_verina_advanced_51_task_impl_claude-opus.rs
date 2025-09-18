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
    /* code modified by LLM (iteration 4): Fixed syntax error in forall quantifiers */
    let mut result = Vec::new();
    let mut i: usize = 0;
    let mut j: usize = 0;
    
    while i < a.len() && j < b.len()
        invariant
            i <= a.len(),
            j <= b.len(),
            is_sorted(result@),
            forall|k: int| 0 <= k < result.len() ==> 
                (exists|ai: int| 0 <= ai < i && result@[k] == a@[ai]) ||
                (exists|bi: int| 0 <= bi < j && result@[k] == b@[bi]),
            forall|ai: int| 0 <= ai < i ==> exists|k: int| 0 <= k < result.len() && result@[k] == a@[ai],
            forall|bi: int| 0 <= bi < j ==> exists|k: int| 0 <= k < result.len() && result@[k] == b@[bi],
            result.len() == i + j,
            forall|k: int| 0 <= k < result.len() - 1 ==> result@[k] <= result@[k + 1],
            i < a.len() ==> forall|k: int| 0 <= k < result.len() ==> result@[k] <= a@[i as int],
            j < b.len() ==> forall|k: int| 0 <= k < result.len() ==> result@[k] <= b@[j as int],
        decreases a.len() + b.len() - i - j
    {
        if a[i] <= b[j] {
            result.push(a[i]);
            i = i + 1;
        } else {
            result.push(b[j]);
            j = j + 1;
        }
    }
    
    while i < a.len()
        invariant
            i <= a.len(),
            j == b.len(),
            is_sorted(result@),
            result.len() == i + j,
            forall|k: int| 0 <= k < result.len() ==> 
                (exists|ai: int| 0 <= ai < i && result@[k] == a@[ai]) ||
                (exists|bi: int| 0 <= bi < b.len() && result@[k] == b@[bi]),
            forall|ai: int| 0 <= ai < i ==> exists|k: int| 0 <= k < result.len() && result@[k] == a@[ai],
            forall|bi: int| 0 <= bi < b.len() ==> exists|k: int| 0 <= k < result.len() && result@[k] == b@[bi],
        decreases a.len() - i
    {
        result.push(a[i]);
        i = i + 1;
    }
    
    while j < b.len()
        invariant
            i == a.len(),
            j <= b.len(),
            is_sorted(result@),
            result.len() == i + j,
            forall|k: int| 0 <= k < result.len() ==> 
                (exists|ai: int| 0 <= ai < a.len() && result@[k] == a@[ai]) ||
                (exists|bi: int| 0 <= bi < j && result@[k] == b@[bi]),
            forall|ai: int| 0 <= ai < a.len() ==> exists|k: int| 0 <= k < result.len() && result@[k] == a@[ai],
            forall|bi: int| 0 <= bi < j ==> exists|k: int| 0 <= k < result.len() && result@[k] == b@[bi],
        decreases b.len() - j
    {
        result.push(b[j]);
        j = j + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}