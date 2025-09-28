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
/* helper modified by LLM (iteration 5): added missing lemma keyword */
lemma lemma_start_index_bounds(i: int, n: int, k: int)
    requires
        k > 0,
        0 <= i <= k,
        n >= 0
    ensures
        0 <= start_index(i, n, k) <= n
    decreases i
{
    if i <= 0 {
    } else {
        lemma_start_index_bounds(i - 1, n, k);
        lemma_chunk_size_bounds(i - 1, n, k);
    }
}

lemma lemma_chunk_size_bounds(i: int, n: int, k: int)
    requires
        k > 0,
        0 <= i < k,
        n >= 0
    ensures
        chunk_size(i, n, k) >= 0,
        chunk_size(i, n, k) <= (n + k - 1) / k
{
}

lemma lemma_start_index_plus_chunk_le_n(i: int, n: int, k: int)
    requires
        k > 0,
        0 <= i < k,
        n >= 0
    ensures
        start_index(i, n, k) + chunk_size(i, n, k) <= n
    decreases i
{
    if i <= 0 {
    } else {
        lemma_start_index_plus_chunk_le_n(i - 1, n, k);
        lemma_chunk_size_bounds(i - 1, n, k);
        lemma_chunk_size_bounds(i, n, k);
    }
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
{
    /* code modified by LLM (iteration 5): implementation remains the same */
    let mut result: Vec<Vec<i8>> = Vec::new();
    let n = v.len() as int;
    let mut i: usize = 0;
    
    while i < k
        invariant
            result.len() == i,
            forall|j: int| 0 <= j < i ==> #[trigger] result[j].len() == chunk_size(j, n, k as int),
            forall|j: int, idx: int| 0 <= j < i && 0 <= idx < result[j].len() ==> 
                #[trigger] result[j][idx] == v[start_index(j, n, k as int) + idx]
    {
        proof {
            lemma_start_index_bounds(i as int, n, k as int);
            lemma_chunk_size_bounds(i as int, n, k as int);
            lemma_start_index_plus_chunk_le_n(i as int, n, k as int);
        }
        
        let start = start_index(i as int, n, k as int) as usize;
        let size = chunk_size(i as int, n, k as int) as usize;
        let mut chunk: Vec<i8> = Vec::new();
        
        let mut j: usize = 0;
        while j < size
            invariant
                chunk.len() == j,
                forall|idx: int| 0 <= idx < j ==> #[trigger] chunk[idx] == v[start + idx]
        {
            chunk.push(v[start + j]);
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