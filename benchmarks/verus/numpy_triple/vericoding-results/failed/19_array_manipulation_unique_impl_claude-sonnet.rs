// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added proof keyword for lemma functions */
proof fn lemma_sorted_insert_maintains_sorted(s: Seq<i32>, val: i32, pos: usize)
    requires
        is_sorted(s),
        pos <= s.len(),
        forall|i: int| 0 <= i < pos ==> s[i] <= val,
        forall|i: int| pos <= i < s.len() ==> val <= s[i],
    ensures
        is_sorted(s.insert(pos as int, val)),
{
}

proof fn lemma_insert_preserves_contains(s: Seq<i32>, val: i32, pos: usize, x: i32)
    requires
        pos <= s.len(),
    ensures
        s.insert(pos as int, val).contains(x) == (x == val || s.contains(x)),
{
}

proof fn lemma_contains_transitivity(s1: Seq<i32>, s2: Seq<i32>, x: i32)
    requires
        s1.contains(x),
        forall|y: i32| s1.contains(y) ==> s2.contains(y),
    ensures
        s2.contains(x),
{
}
// </vc-helpers>

// <vc-spec>
spec fn is_sorted(arr: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < arr.len() ==> arr[i] <= arr[j]
}

spec fn has_no_duplicates(arr: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < arr.len() && 0 <= j < arr.len() && i != j ==> arr[i] != arr[j]
}

spec fn all_elements_from_input(result: Seq<i32>, input: Seq<i32>) -> bool {
    forall|i: int| 0 <= i < result.len() ==> #[trigger] input.contains(result[i])
}

spec fn all_distinct_elements_present(input: Seq<i32>, result: Seq<i32>) -> bool {
    forall|val: i32| input.contains(val) ==> #[trigger] result.contains(val)
}

fn numpy_unique(arr: Vec<i32>) -> (result: (usize, Vec<i32>))
    ensures
        is_sorted(result.1@),
        has_no_duplicates(result.1@),
        all_elements_from_input(result.1@, arr@),
        all_distinct_elements_present(arr@, result.1@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added decreases clauses to all loops */
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0;
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            is_sorted(result@),
            has_no_duplicates(result@),
            all_elements_from_input(result@, arr@),
            forall|val: i32| (exists|k: int| 0 <= k < i && arr@[k] == val) ==> result@.contains(val),
        decreases arr.len() - i
    {
        let current = arr[i];
        let mut found = false;
        let mut j = 0;
        
        while j < result.len()
            invariant
                0 <= j <= result.len(),
                found == (exists|k: int| 0 <= k < j && result@[k] == current),
                is_sorted(result@),
                has_no_duplicates(result@),
            decreases result.len() - j
        {
            if result[j] == current {
                found = true;
                break;
            }
            j += 1;
        }
        
        if !found {
            let mut insert_pos = 0;
            
            while insert_pos < result.len()
                invariant
                    0 <= insert_pos <= result.len(),
                    forall|k: int| 0 <= k < insert_pos ==> result@[k] <= current,
                    is_sorted(result@),
                decreases result.len() - insert_pos
            {
                if result[insert_pos] > current {
                    break;
                }
                insert_pos += 1;
            }
            
            proof {
                lemma_sorted_insert_maintains_sorted(result@, current, insert_pos);
                lemma_insert_preserves_contains(result@, current, insert_pos, current);
            }
            
            result.insert(insert_pos, current);
        }
        
        i += 1;
    }
    
    (result.len(), result)
}
// </vc-code>


}
fn main() {}