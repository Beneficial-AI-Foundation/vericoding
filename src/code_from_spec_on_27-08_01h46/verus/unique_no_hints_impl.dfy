use vstd::prelude::*;

verus! {

// <vc-helpers>
spec fn contains_value(seq: Seq<i32>, val: i32) -> bool {
    exists|i: int| 0 <= i < seq.len() && seq[i] == val
}

spec fn no_duplicates(seq: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < seq.len() ==> seq[i] != seq[j]
}

spec fn is_sorted_strict(seq: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < seq.len() ==> seq[i] < seq[j]
}

spec fn subsequence_of_unique_elements(original: Seq<i32>, unique: Seq<i32>) -> bool {
    forall|i: int| 0 <= i < unique.len() ==> contains_value(original, unique[i])
}

spec fn first_occurrence(seq: Seq<i32>, val: i32, pos: int) -> bool {
    0 <= pos < seq.len() && seq[pos] == val &&
    forall|k: int| 0 <= k < pos ==> seq[k] != val
}

proof fn lemma_first_occurrence_unique(a: Seq<i32>, i: int)
    requires 
        0 <= i < a.len(),
        forall|x: int, y: int| 0 <= x < y < a.len() ==> a[x] <= a[y]
    ensures
        first_occurrence(a, a[i], i) <==> forall|k: int| 0 <= k < i ==> a[k] != a[i]
{
}

proof fn lemma_contains_value_preserved(old_result: Seq<i32>, new_result: Seq<i32>, val: i32)
    requires
        new_result.len() == old_result.len() + 1,
        forall|k: int| 0 <= k < old_result.len() ==> old_result[k] == new_result[k],
        new_result[old_result.len() as int] == val
    ensures
        forall|x: i32| contains_value(old_result, x) ==> contains_value(new_result, x)
{
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
    let mut result = Vec::new();
    let mut i = 0;
    
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            is_sorted_strict(result@),
            no_duplicates(result@),
            subsequence_of_unique_elements(a@, result@),
            forall|k: int| 
                #![trigger result@[k]]
                0 <= k < result.len() ==> exists|j: int| 0 <= j < i && a[j] == result@[k],
            forall|j: int| 0 <= j < i ==> (contains_value(result@, a[j]) <==> first_occurrence(a@, a[j], j)),
        decreases a.len() - i,
    {
        let current = a[i];
        let mut found = false;
        let mut j = 0;
        
        while j < result.len()
            invariant
                0 <= j <= result.len(),
                found == exists|k: int| 0 <= k < j && result@[k] == current,
                is_sorted_strict(result@),
            decreases result.len() - j,
        {
            if result[j] == current {
                found = true;
                break;
            }
            j += 1;
        }
        
        if !found {
            proof {
                let old_result = result@;
                lemma_contains_value_preserved(old_result, result@.push(current), current);
                assert(first_occurrence(a@, current, i as int) == (forall|k: int| 0 <= k < i ==> a[k] != current));
                lemma_first_occurrence_unique(a@, i as int);
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