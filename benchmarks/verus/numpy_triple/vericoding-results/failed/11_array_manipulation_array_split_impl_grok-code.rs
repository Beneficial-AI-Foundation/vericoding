// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn chunk_size(i: int, n: int, k: int) -> int {
    if i < n % k {
        (n + k - 1) / k
    } else {
        n / k
    }
}

spec fn start_index(i: int, n: int, k: int) -> int 
    decreases i
{
    if i <= 0 {
        0
    } else {
        start_index(i - 1, n, k) + chunk_size(i - 1, n, k)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Adjusted multi-line if expression formatting by placing the if on a new line after the assignment to fix compilation error */
fn get_chunk_size(i: usize, n: usize, k: usize) -> (res: usize)
    requires k > 0,
    ensures res as int == chunk_size(i as int, n as int, k as int)
{
    let modulus: int = (n as int) % (k as int);
    let res_int: int =
        if i as int < modulus {
            (n as int + k as int - 1) / (k as int)
        } else {
            (n as int) / (k as int)
        };
    res_int as usize
}

/* helper modified by LLM (iteration 5): unchanged as no errors */
fn get_start_index(i: usize, n: usize, k: usize) -> (res: usize)
    requires k > 0,
    ensures
        res as int == start_index(i as int, n as int, k as int),
        res as int <= usize::MAX as int
{
    let mut sum: int = 0;
    let mut j: int = 0;
    while j < (i as int)
        invariant
            sum == start_index(j, n as int, k as int),
            0 <= j <= i as int,
        decreases i as int - j
    {
        let size: int = get_chunk_size(j as usize, n, k) as int;
        sum += size;
        j += 1;
    }
    sum as usize
}
// </vc-helpers>

// <vc-spec>
fn array_split(v: Vec<i8>, k: usize) -> (result: Vec<Vec<i8>>)
    requires k > 0,
    ensures
        result.len() == k,
        /* Each sub-vector has the correct size based on its position */
        forall|i: int| 0 <= i < k as int ==> #[trigger] result[i].len() == chunk_size(i, v.len() as int, k as int),
        /* Elements are preserved in order across all sub-vectors */
        forall|i: int, j: int| 0 <= i < k as int && 0 <= j < result[i].len() ==> 
            #[trigger] result[i][j] == v[start_index(i, v.len() as int, k as int) + j]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): unchanged as no errors in vc-code */
{
    let mut result = Vec::new();
    for i in 0..k {
        let start = get_start_index(i, v.len(), k);
        let size = get_chunk_size(i, v.len(), k);
        let mut chunk = Vec::new();
        for j in 0..size {
            chunk.push(v[start + j]);
        }
        result.push(chunk);
    }
    result
}
// </vc-code>


}
fn main() {}