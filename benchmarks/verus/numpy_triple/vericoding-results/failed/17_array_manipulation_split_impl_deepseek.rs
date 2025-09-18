// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn vec_split_helper(arr: Seq<f32>, k: nat, n: nat) 
    requires k > 0, arr.len() % k == 0, n <= arr.len(),
    ensures 
        forall|i: int, j: int| 0 <= i < k as int && 0 <= j < (arr.len() / k) as int && i * (arr.len() / k) as int + j < n as int ==> {
            let idx = i * (arr.len() / k) as int + j;
            idx < arr.len() as int && #[trigger] arr[idx] == arr[idx]
        }
    decreases n
{
    if n > 0 {
        vec_split_helper(arr, k, (n - 1) as nat);
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
    /* code modified by LLM (iteration 5): Added decreases clause to while loop */
    let n: usize = arr.len();
    let chunk_size: usize = n / k;
    let mut result = Vec::<Vec<f32>>::new();
    
    proof {
        vec_split_helper(arr@, k as nat, n as nat);
    }
    
    let mut i: usize = 0;
    while i < k
        decreases k - i
        invariant
            0 <= i <= k,
            result.len() == i,
            forall|idx: int| 0 <= idx < i as int ==> result@[idx].len() == chunk_size as int,
            forall|outer_idx: int, inner_idx: int| 
                0 <= outer_idx < i as int && 0 <= inner_idx < chunk_size as int ==> {
                    let original_idx: int = outer_idx * chunk_size as int + inner_idx;
                    0 <= original_idx < n as int && result@[outer_idx][inner_idx] == arr@[original_idx]
                }
    {
        let start: usize = i * chunk_size;
        let end: usize = start + chunk_size;
        let mut chunk = Vec::<f32>::new();
        let mut j: usize = start;
        while j < end
            decreases end - j
            invariant
                start <= j <= end,
                chunk.len() == j - start,
                forall|idx: int| 0 <= idx < (j - start) as int ==> chunk@[idx] == arr@[start as int + idx]
        {
            chunk.push(arr[j]);
            j += 1;
        }
        result.push(chunk);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}