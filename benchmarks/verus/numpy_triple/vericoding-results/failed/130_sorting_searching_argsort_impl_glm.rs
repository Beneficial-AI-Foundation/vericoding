// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn argsort(a: Vec<i32>) -> (result: Vec<usize>)
    ensures 
        result.len() == a.len(),

        forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i] < a.len(),

        forall|i: int, j: int| 0 <= i < j < result.len() ==> 
            a[#[trigger] result[i] as int] <= a[#[trigger] result[j] as int],

        forall|i: int, j: int| 0 <= i < j < result.len() && 
            a[#[trigger] result[i] as int] == a[#[trigger] result[j] as int] ==> 
            result[i] < result[j]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed missing braces around method body */
    let mut arr_with_index: Vec<(i32, usize)> = Vec::new();
    for i in 0..a.len() {
        arr_with_index.push((a[i], i));
    }

    let n = arr_with_index.len();
    for i in 1..n {
        let key = arr_with_index[i];
        let mut j = i;
        while j > 0 {
            let prev_index = j - 1;
            if arr_with_index[prev_index].0 > key.0 || (arr_with_index[prev_index].0 == key.0 && arr_with_index[prev_index].1 > key.1) {
                arr_with_index[j] = arr_with_index[prev_index];
                j = prev_index;
            } else {
                break;
            }
        }
        arr_with_index[j] = key;
    }

    let mut result: Vec<usize> = Vec::new();
    for (_, idx) in arr_with_index.into_iter() {
        result.push(idx);
    }
    result
}
// </vc-code>

}
fn main() {}