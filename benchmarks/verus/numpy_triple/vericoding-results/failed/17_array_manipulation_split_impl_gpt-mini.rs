// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): compute chunk size */
fn chunk_size(arr_len: nat, k: nat) -> nat { arr_len / k }

/* helper modified by LLM (iteration 5): divisibility lemma for exact division */
proof fn div_exact(arr_len: nat, k: nat) requires k > 0 && arr_len % k == 0 ensures arr_len == k * (arr_len / k) {
    proof {
        assert(arr_len == k * (arr_len / k) + arr_len % k);
        assert(arr_len % k == 0);
        assert(k * (arr_len / k) + 0 == k * (arr_len / k));
        assert(arr_len == k * (arr_len / k));
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
    /* code modified by LLM (iteration 5): implement splitting array into k equal chunks using nested loops */
    let n = arr.len();
    let chunk = n / k;
    let mut result: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;
    while i < k
        invariant i <= k && result.len() == i;
        decreases k - i
    {
        let mut v: Vec<f32> = Vec::new();
        let mut j: usize = 0;
        while j < chunk
            invariant j <= chunk && v.len() == j;
            decreases chunk - j
        {
            let idx = i * chunk + j;
            assert(idx < n);
            v.push(arr[idx]);
            j += 1;
        }
        result.push(v);
        i += 1;
    }
    result
}
// </vc-code>

}
fn main() {}