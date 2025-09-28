// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

/* helper modified by LLM (iteration 5): Fixed lemma signatures with proper parameter and return types */
proof fn lemma_div_pos(a: int, b: int)
    requires
        a >= 0,
        b > 0,
    ensures
        a / b >= 0,
{
}

proof fn lemma_mul_div_eq(a: int, b: int)
    requires
        b > 0,
    ensures
        a == b * (a / b) + a % b,
        a % b >= 0,
        a % b < b,
{
}

proof fn lemma_div_mod_properties(a: int, b: int)
    requires
        b > 0,
    ensures
        a / b == (a - a % b) / b,
        a == b * (a / b) + a % b,
{
}

fn get_chunk_size(arr_len: usize, k: usize) -> (chunk_size: usize)
    requires
        k > 0,
        arr_len % k == 0,
    ensures
        chunk_size == arr_len / k,
{
    arr_len / k
}

proof fn lemma_int_to_usize(n: int)
    requires
        0 <= n,
    ensures
        n as usize >= 0,
{
}

proof fn lemma_usize_to_int(n: usize)
    ensures
        n as int >= 0,
{
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
    /* code modified by LLM (iteration 5): Fixed integer casting issues and lemma calls with proper types */
    let arr_len = arr.len();
    let chunk_size = get_chunk_size(arr_len, k);
    let mut result: Vec<Vec<f32>> = Vec::with_capacity(k);
    let mut i: usize = 0;
    
    while i < k
        invariant
            i <= k,
            result.len() == i,
            forall|idx: int| 0 <= idx < i ==> #[trigger] result[idx].len() == chunk_size,
            forall|idx_i: int, idx_j: int| 
                0 <= idx_i < i && 0 <= idx_j < chunk_size as int ==> {
                    let arr_idx = idx_i * chunk_size as int + idx_j;
                    proof { lemma_usize_to_int(chunk_size); lemma_int_to_usize(chunk_size as int); }
                    proof { lemma_usize_to_int(arr_len); }
                    0 <= arr_idx < arr_len as int && #[trigger] result[idx_i][idx_j] == arr[arr_idx as usize]
                },
        decreases k - i,
    {
        let mut chunk: Vec<f32> = Vec::with_capacity(chunk_size);
        let mut j: usize = 0;
        
        while j < chunk_size
            invariant
                j <= chunk_size,
                chunk.len() == j,
                forall|idx: int| 0 <= idx < j ==> {
                    let pos = i * chunk_size + idx;
                    proof { lemma_usize_to_int(pos); lemma_int_to_usize(pos as int); }
                    #[trigger] chunk[idx] == arr[pos as usize]
                },
            decreases chunk_size - j,
        {
            let idx = i * chunk_size + j;
            proof { lemma_usize_to_int(idx); }
            chunk.push(arr[idx as usize]);
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