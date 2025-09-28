// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
    /* code modified by LLM (iteration 5): Fixed type mismatches with usize/int conversions */
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    
    while i < arr.len()
        invariant
            i <= arr.len(),
            result.len() <= i,
            forall|j: int| 0 <= j < result.len() - 1 ==> #[trigger] result[j] < result[j + 1],
            forall|x: i32| result@.contains(x) ==> arr@.subrange(0, i as int).contains(x),
            forall|x: i32| arr@.subrange(0, i as int).contains(x) ==> result@.contains(x),
        decreases arr.len() - i
    {
        let val = arr[i];
        let mut already_present = false;
        let mut j: usize = 0;
        
        while j < result.len()
            invariant
                j <= result.len(),
                already_present <==> result@.subrange(0, j as int).contains(val),
            decreases result.len() - j
        {
            if result[j] == val {
                already_present = true;
                assert(result[j as int] == val);
                assert(result@.subrange(0, j + 1).contains(val));
            }
            j = j + 1;
        }
        
        if !already_present {
            let mut insert_pos: usize = 0;
            
            while insert_pos < result.len() && result[insert_pos] < val
                invariant
                    insert_pos <= result.len(),
                    forall|k: int| 0 <= k < insert_pos ==> result[k] < val,
                    forall|k: int| insert_pos as int <= k < result.len() ==> result[k] >= val || result[insert_pos as int] >= val,
                decreases result.len() - insert_pos
            {
                insert_pos = insert_pos + 1;
            }
            
            result.insert(insert_pos, val);
            
            proof {
                assert(result[insert_pos as int] == val);
                assert(result@.contains(val));
                assert(forall|k: int| 0 <= k < insert_pos ==> result[k] < val);
                assert(forall|k: int| insert_pos as int < k <= result.len() - 1 ==> result[k] > val);
                assert(forall|j: int| 0 <= j < result.len() - 1 ==> result[j] < result[j + 1]);
            }
        }
        
        i = i + 1;
    }
    
    proof {
        assert(i == arr.len());
        assert(arr@.subrange(0, arr.len() as int) =~= arr@);
        assert(forall|x: i32| arr@.contains(x) ==> result@.contains(x));
        assert(forall|x: i32| result@.contains(x) ==> arr@.contains(x));
    }
    
    result
}
// </vc-code>

}
fn main() {}