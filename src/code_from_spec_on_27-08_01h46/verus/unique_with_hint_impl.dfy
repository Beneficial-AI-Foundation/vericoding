use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn contains_value(s: Seq<i32>, val: i32) -> bool {
    exists|i: int| 0 <= i < s.len() && s[i] == val
}

spec fn no_duplicates(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> s[i] != s[j]
}

spec fn is_subsequence_of_unique_elements(original: &[i32], result: Seq<i32>) -> bool {
    forall|i: int| 0 <= i < result.len() ==> contains_value(original@, result[i])
}

spec fn all_processed_contained_or_duplicate(a: &[i32], result: Seq<i32>, processed: int) -> bool {
    forall|j: int| 0 <= j < processed ==> (contains_value(result, a[j]) || exists|k: int| 0 <= k < j && a[k] == a[j])
}

proof fn lemma_element_position(a: &[i32], result: Seq<i32>, val: i32, cur_idx: int)
    requires
        forall|i: int, j: int| 0 <= i && i < j && j < a.len() ==> a[i] <= a[j],
        contains_value(result, val),
        0 <= cur_idx < a.len(),
        a[cur_idx] == val,
        all_processed_contained_or_duplicate(a, result, cur_idx),
    ensures
        exists|n: int| 0 <= n < cur_idx && a[n] == val,
{
    assert(contains_value(result, val));
    let witness_idx = choose|k: int| 0 <= k < result.len() && result[k] == val;
    assert(contains_value(a@, result[witness_idx]));
    let orig_pos = choose|p: int| 0 <= p < a.len() && a[p] == result[witness_idx];
    if orig_pos >= cur_idx {
        assert(a[orig_pos] == val && a[cur_idx] == val);
        assert(forall|i: int, j: int| 0 <= i && i < j && j < a.len() ==> a[i] <= a[j]);
        if orig_pos > cur_idx {
            assert(a[cur_idx] <= a[orig_pos]);
            assert(val <= val);
        }
        assert(all_processed_contained_or_duplicate(a, result, cur_idx));
        assert(contains_value(result, a[cur_idx]) || exists|k: int| 0 <= k < cur_idx && a[k] == a[cur_idx]);
        assert(contains_value(result, val));
        if !exists|k: int| 0 <= k < cur_idx && a[k] == val {
            assert(false);
        }
    }
}
// </vc-helpers>

// <vc-spec>
#[verifier::loop_isolation(false)]
fn unique(a: &[i32]) -> (result: Vec<i32>)
    requires
        forall|i: int, j: int|
            #![trigger a[i], a[j]]
            0 <= i && i < j && j < a.len() ==> a[i] <= a[j],
    ensures
        forall|i: int, j: int|
            #![trigger result[i], result[j]]
            0 <= i && i < j && j < result.len() ==> result[i] < result[j],
// </vc-spec>

// <vc-code>
{
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            forall|k: int, l: int|
                #![trigger result@[k], result@[l]]
                0 <= k < l < result.len() ==> result@[k] < result@[l],
            forall|k: int| 0 <= k < result.len() ==> contains_value(a@, result@[k]),
            no_duplicates(result@),
            all_processed_contained_or_duplicate(a, result@, i as int),
        decreases a.len() - i,
    {
        let current = a[i];
        let mut found = false;
        let mut j = 0;
        
        while j < result.len()
            invariant
                0 <= j <= result.len(),
                found ==> exists|k: int| 0 <= k < j && result@[k] == current,
                !found ==> forall|k: int| 0 <= k < j ==> result@[k] != current,
                forall|k: int, l: int|
                    #![trigger result@[k], result@[l]]
                    0 <= k < l < result.len() ==> result@[k] < result@[l],
            decreases result.len() - j,
        {
            if result[j] == current {
                found = true;
            }
            j += 1;
        }
        
        if !found {
            proof {
                assert(forall|k: int| 0 <= k < result.len() ==> result@[k] != current);
                if result.len() > 0 {
                    let last_idx = (result.len() - 1) as int;
                    assert(result@[last_idx] < current) by {
                        assert(contains_value(a@, result@[last_idx]));
                        let m = choose|p: int| 0 <= p < a.len() && a[p] == result@[last_idx];
                        assert(0 <= m < a.len() && a[m] == result@[last_idx]);
                        if m >= i {
                            lemma_element_position(a, result@, result@[last_idx], m as int);
                            let n = choose|q: int| 0 <= q < m && a[q] == result@[last_idx];
                            assert(0 <= n < i);
                        } else {
                            assert(0 <= m < i);
                        }
                        let n = if m >= i {
                            choose|q: int| 0 <= q < m && a[q] == result@[last_idx]
                        } else {
                            m
                        };
                        assert(0 <= n < i);
                        assert(a[n] == result@[last_idx]);
                        assert(n < i);
                        assert(a[n] <= a[i]);
                        assert(result@[last_idx] <= current);
                        assert(!contains_value(result@, current));
                        if result@[last_idx] == current {
                            assert(contains_value(result@, current));
                            assert(false);
                        }
                        assert(result@[last_idx] < current);
                    };
                }
            }
            result.push(current);
        }
        
        i += 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}