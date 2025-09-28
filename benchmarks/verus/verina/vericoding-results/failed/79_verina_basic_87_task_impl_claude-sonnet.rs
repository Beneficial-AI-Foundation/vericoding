// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn sorted_property_preserved(a: &Vec<i32>, result: &Vec<i32>, sorted_len: usize)
    requires
        sorted_len <= a.len(),
        result.len() == a.len(),
        forall|i: int, j: int| 0 <= i <= j < sorted_len ==> result[i] <= result[j],
        forall|i: int| sorted_len <= i < result.len() ==> exists|j: int| 0 <= j < a.len() && result[i as int] == a[j],
        forall|i: int| 0 <= i < sorted_len ==> exists|j: int| 0 <= j < a.len() && result[i] == a[j],
    ensures
        true,
{}

/* helper modified by LLM (iteration 5): removed invalid trigger attribute */
proof fn multiset_property_after_swap(a: Seq<i32>, result: Seq<i32>, i: int, min_idx: int, new_result: Seq<i32>)
    requires
        0 <= i < result.len(),
        0 <= min_idx < result.len(),
        result.len() == a.len(),
        result =~= a,
        new_result == result.update(i, result[min_idx]).update(min_idx, result[i]),
    ensures
        new_result =~= a,
{}
// </vc-helpers>

// <vc-spec>
fn selection_sort(a: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() == a.len(),
        forall|i: int, j: int| 0 <= i <= j < result.len() ==> result[i] <= result[j],
        result@ =~= a@,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): removed trigger annotation that caused compilation error */
    let mut result = a.clone();
    let mut i = 0;
    
    while i < result.len()
        invariant
            result.len() == a.len(),
            i <= result.len(),
            forall|x: int, y: int| 0 <= x <= y < i ==> result[x] <= result[y],
            result@ =~= a@,
        decreases result.len() - i
    {
        let mut min_idx = i;
        let mut j = i + 1;
        
        while j < result.len()
            invariant
                i <= min_idx < result.len(),
                i < j <= result.len(),
                result.len() == a.len(),
                forall|k: int| i <= k < j ==> result[min_idx as int] <= result[k],
                result@ =~= a@,
            decreases result.len() - j
        {
            if result[j] < result[min_idx] {
                min_idx = j;
            }
            j += 1;
        }
        
        if min_idx != i {
            let temp = result[i];
            let ghost old_result = result@;
            result.set(i, result[min_idx]);
            result.set(min_idx, temp);
            
            proof {
                let new_result = old_result.update(i as int, old_result[min_idx as int]).update(min_idx as int, old_result[i as int]);
                multiset_property_after_swap(a@, old_result, i as int, min_idx as int, new_result);
                assert(result@ =~= a@);
            }
        }
        
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}