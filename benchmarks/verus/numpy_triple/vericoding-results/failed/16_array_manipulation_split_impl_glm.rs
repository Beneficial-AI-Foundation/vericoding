// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): changed 'pred' to 'predicate' */
predicate valid_split(result: Vec<Vec<f32>>, arr: Vec<f32>, n: usize, i: int) {
    result.len() == i as usize &&
    forall|idx: int| 0 <= idx < i ==> {
        result[idx].len() == n &&
        forall|j: int| 0 <= j < n as int ==> {
            let index = (idx * (n as int) + j) as usize;
            result[idx][j as usize] == arr[index]
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn split(arr: Vec<f32>, k: usize) -> (result: Vec<Vec<f32>>)
    requires
        k > 0,
        arr.len() % k == 0,
    ensures
        result.len() == k,
        forall|i: int| #[trigger] result[i].len() == (arr.len() / k) ==> (0 <= i < k),
        forall|i: int, j: int| 
            0 <= i < k && 0 <= j < (arr.len() / k) as int ==> {
                let idx = i * (arr.len() / k) as int + j;
                0 <= idx < arr.len() as int && #[trigger] result[i][j] == arr[idx]
            },
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): no changes needed */
    let k_int = k as int;
    let n = arr.len() / k;
    let mut result = Vec::new();
    let mut i = 0 as int;
    while i < k_int
        invariant
            0 <= i <= k_int,
            valid_split(result, arr, n, i)
        decreases (k_int - i)
    {
        let start = (i as usize) * n;
        let end = start + n;
        let subvec = arr[start..end].to_vec();
        result.push(subvec);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}