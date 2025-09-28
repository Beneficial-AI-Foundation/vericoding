// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed trigger issue by using single trigger per quantifier */
spec fn is_sorted(s: Seq<i32>) -> bool {
    forall|i: int| 0 <= i < s.len() - 1 ==> #[trigger] s[i] <= s[i + 1]
}

spec fn has_no_duplicates(s: Seq<i32>) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> #[trigger] s[i] != s[j]
}

fn vec_contains(v: &Vec<i32>, x: i32) -> (found: bool)
    ensures found == v@.contains(x)
{
    let mut i = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            !v@.subrange(0, i as int).contains(x)
        decreases v.len() - i
    {
        if v[i] == x {
            return true;
        }
        i += 1;
    }
    false
}
// </vc-helpers>

// <vc-spec>
fn unique_sorted(arr: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() <= arr.len(),
        forall|i: int| 0 <= i < result.len() - 1 ==> #[trigger] result[i] <= result[i + 1],
        forall|x: i32| arr@.contains(x) <==> result@.contains(x),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed trigger annotations to avoid arithmetic/non-arithmetic conflict */
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0;
    
    while i < arr.len()
        invariant
            0 <= i <= arr.len(),
            is_sorted(result@),
            has_no_duplicates(result@),
            forall|x: i32| result@.contains(x) ==> arr@.contains(x),
            forall|x: i32| arr@.subrange(0, i as int).contains(x) ==> result@.contains(x),
        decreases arr.len() - i
    {
        let current = arr[i];
        
        if !vec_contains(&result, current) {
            let mut j = 0;
            let mut inserted = false;
            
            while j < result.len() && !inserted
                invariant
                    0 <= j <= result.len(),
                    !inserted ==> forall|k: int| 0 <= k < j ==> #[trigger] result[k] < current,
                decreases result.len() - j
            {
                if result[j] > current {
                    result.insert(j, current);
                    inserted = true;
                } else {
                    j += 1;
                }
            }
            
            if !inserted {
                result.push(current);
            }
        }
        
        i += 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}