use vstd::prelude::*;

verus! {

spec fn in_array(a: Seq<i32>, x: i32) -> (ret: bool) {
    exists|i: int| 0 <= i < a.len() && a[i] == x
}

// <vc-helpers>
spec fn in_array_seq(a: Seq<i32>, x: i32) -> bool {
    exists|i: int| 0 <= i < a.len() && a[i] == x
}

proof fn lemma_seq_subset_len(s1: Seq<i32>, s2: Seq<i32>)
    requires
        forall|i: int| 0 <= i < s1.len() ==> in_array_seq(s2, s1[i]),
    ensures
        s1.len() <= s2.len(),
{
}

proof fn lemma_no_duplicates_len(s: Seq<i32>)
    ensures
        s.len() <= s.len(),
{
}

spec fn contains_at_index(v: Vec<i32>, i: int, x: i32) -> bool {
    0 <= i < v.len() && v[i] == x
}

spec fn is_unique(v: Vec<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < v.len() ==> v[i] != v[j]
}

spec fn all_elements_from_array(v: Vec<i32>, a: Seq<i32>) -> bool {
    forall|i: int| 0 <= i < v.len() ==> in_array_seq(a, v[i])
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn remove_duplicates(a: &[i32]) -> (result: Vec<i32>)
    // pre-conditions-start
    requires
        a.len() >= 1,
    // pre-conditions-end
    // post-conditions-start
    ensures
        forall|i: int| #![auto] 0 <= i < result.len() ==> in_array(a@, result[i]),
        forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut seen = Vec::new();
    
    let mut idx = 0;
    while idx < a.len()
        invariant
            idx <= a.len(),
            forall|i: int| 0 <= i < result.len() ==> in_array_seq(a@, result[i]),
            forall|i: int, j: int| 0 <= i < j < result.len() ==> result[i] != result[j],
            forall|i: int| 0 <= i < seen.len() ==> in_array_seq(a@, seen[i]),
            forall|i: int, j: int| 0 <= i < j < seen.len() ==> seen[i] != seen[j],
            result.len() == seen.len(),
            forall|k: int| 0 <= k < result.len() ==> result[k] == seen[k],
    {
        let current = a[idx];
        let mut found = false;
        let mut j = 0;
        
        while j < seen.len()
            invariant
                j <= seen.len(),
                found == (exists|k: int| 0 <= k < j && seen[k] == current),
        {
            if seen[j] == current {
                found = true;
                break;
            }
            j += 1;
        }
        
        if !found {
            seen.push(current);
            result.push(current);
        }
        
        idx += 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}