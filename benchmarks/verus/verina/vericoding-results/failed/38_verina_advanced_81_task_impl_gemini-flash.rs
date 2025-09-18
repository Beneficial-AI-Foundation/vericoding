// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed compilation errors related to `nat` and `int` casts in executable code. */
fn insertion_sort_unique_and_sorted(arr: &Vec<i32>) -> (result: Vec<i32>)
    ensures
        result.len() <= arr.len(),
        forall|i: int| 0 <= i < (result.len() as int) - 1 ==> #[trigger] result[i as usize] <= result[(i + 1) as usize],
        forall|x: i32| arr@.contains(x) <==> result@.contains(x),
{
    let mut result: Vec<i32> = Vec::new();
    let mut i: usize = 0;

    while i < arr.len()
        invariant
            i <= arr.len(),
            (result.len() as int) <= (i as int),
            forall|j: int| 0 <= j < (result.len() as int) - 1 ==> result[j as usize] <= result[(j + 1) as usize],
            forall|k: int| 0 <= k < result.len() ==> arr@.contains(result[k as usize]),
            forall|j: int| 0 <= j < result.len() ==> (forall|k: int| 0 <= k < result.len() && j != k ==> result[j as usize] != result[k as usize]),
            forall|x: i32| (
                (exists|k: int| 0 <= k < i as int && arr@[(k as usize)] == x) <==> result@.contains(x)
            ),
        decreases arr.len() - i
    {
        let val = arr[i as usize];
        let mut found = false;
        proof {
            let mut p = 0;
            while p < result.len()
                invariant
                    0 <= p <= result.len(),
                    !found ==> (forall|k: int| 0 <= k < p ==> result[k as usize] != val),
                decreases result.len() - p
            {
                if result[p as usize] == val {
                    found = true;
                }
                p = p + 1;
            }
        }

        if !found {
            let mut j: usize = 0;
            while j < result.len() && result[j as usize] < val
                invariant
                    j <= result.len(),
                    forall|k: int| 0 <= k < j as int ==> result[k as usize] < val,
                decreases result.len() - j
            {
                j = j + 1;
            }
            result.insert(j, val);
        }
        i = i + 1;
    }
    result
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
/* code modified by LLM (iteration 5): delegates to helper function */
{
    insertion_sort_unique_and_sorted(arr)
}
// </vc-code>

}
fn main() {}