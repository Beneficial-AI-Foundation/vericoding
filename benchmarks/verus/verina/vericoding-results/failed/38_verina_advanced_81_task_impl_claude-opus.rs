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
    /* code modified by LLM (iteration 5): Fixed loop invariants and added assertions for verification */
    let mut result: Vec<i32> = Vec::new();
    let mut i = 0;
    while i < arr.len()
        invariant
            i <= arr.len(),
            result.len() <= i,
            forall|j: int| 0 <= j < result.len() - 1 ==> #[trigger] result[j] < result[j + 1],
            forall|x: i32| result@.contains(x) ==> arr@.subrange(0, i as int).contains(x),
            forall|x: i32| #![auto] arr@.subrange(0, i as int).contains(x) ==> result@.contains(x) || exists|k: int| i <= k < arr.len() && arr[k] == x,
        decreases arr.len() - i
    {
        let val = arr[i];
        let mut already_present = false;
        let mut j = 0;
        while j < result.len()
            invariant
                j <= result.len(),
                already_present <==> result@.subrange(0, j as int).contains(val),
                !already_present ==> forall|k: int| 0 <= k < j ==> result[k] != val,
            decreases result.len() - j
        {
            if result[j] == val {
                already_present = true;
                proof {
                    assert(result@.subrange(0, j + 1).contains(val));
                }
                break;
            }
            j = j + 1;
        }
        
        if !already_present {
            let mut insert_pos = result.len();
            let mut k = 0;
            while k < result.len()
                invariant
                    k <= result.len(),
                    insert_pos <= result.len(),
                    forall|m: int| 0 <= m < k ==> result[m] < val,
                    insert_pos < result.len() ==> result[insert_pos as int] > val,
                    insert_pos == result.len() ==> forall|m: int| 0 <= m < result.len() ==> result[m] < val,
                decreases result.len() - k
            {
                if result[k] > val {
                    insert_pos = k;
                    break;
                }
                k = k + 1;
            }
            result.insert(insert_pos, val);
            proof {
                assert(result[insert_pos as int] == val);
                assert(forall|j: int| 0 <= j < insert_pos ==> result[j] < val);
                assert(forall|j: int| insert_pos < j < result.len() ==> result[j] > val);
            }
        }
        i = i + 1;
    }
    proof {
        assert(forall|x: i32| arr@.contains(x) ==> result@.contains(x));
        assert(forall|x: i32| result@.contains(x) ==> arr@.contains(x));
    }
    result
}
// </vc-code>

}
fn main() {}