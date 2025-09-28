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
/* helper modified by LLM (iteration 5): Fixed lemma proofs and added helper for chunk size bounds */
proof fn lemma_chunk_size_bounds(i: int, n: int, k: int)
    requires
        0 <= i < k,
        k > 0,
        n >= 0,
    ensures
        0 <= chunk_size(i, n, k) <= n,
        chunk_size(i, n, k) <= (n + k - 1) / k,
{
    if i < n % k {
        assert(chunk_size(i, n, k) == (n + k - 1) / k);
    } else {
        assert(chunk_size(i, n, k) == n / k);
    }
}

proof fn lemma_start_index_bounds(i: int, n: int, k: int)
    requires
        0 <= i <= k,
        k > 0,
        n >= 0,
    ensures
        0 <= start_index(i, n, k) <= n,
    decreases i
{
    if i <= 0 {
        assert(start_index(i, n, k) == 0);
    } else {
        lemma_start_index_bounds(i - 1, n, k);
        if i - 1 < k {
            lemma_chunk_size_bounds(i - 1, n, k);
        }
        assert(start_index(i, n, k) == start_index(i - 1, n, k) + chunk_size(i - 1, n, k));
        if i == k {
            lemma_chunk_sizes_sum_to_n(n, k);
        }
    }
}

proof fn lemma_start_index_plus_chunk_size(i: int, n: int, k: int)
    requires
        0 <= i < k,
        k > 0,
        n >= 0,
    ensures
        start_index(i + 1, n, k) == start_index(i, n, k) + chunk_size(i, n, k),
{
    assert(start_index(i + 1, n, k) == start_index(i, n, k) + chunk_size(i, n, k));
}

proof fn lemma_chunk_sizes_sum_to_n(n: int, k: int)
    requires
        k > 0,
        n >= 0,
    ensures
        start_index(k, n, k) == n,
    decreases k
{
    if k == 1 {
        assert(start_index(0, n, k) == 0);
        assert(chunk_size(0, n, k) == n);
        assert(start_index(1, n, k) == n);
    } else {
        lemma_chunk_sizes_sum_to_n_recursive(k, n, k);
    }
}

proof fn lemma_chunk_sizes_sum_to_n_recursive(i: int, n: int, k: int)
    requires
        0 <= i <= k,
        k > 0,
        n >= 0,
    ensures
        i == k ==> start_index(i, n, k) == n,
    decreases i
{
    if i == 0 {
        assert(start_index(0, n, k) == 0);
    } else {
        lemma_chunk_sizes_sum_to_n_recursive(i - 1, n, k);
        assert(start_index(i, n, k) == start_index(i - 1, n, k) + chunk_size(i - 1, n, k));
        
        if i == k {
            let mut sum = 0;
            let mut j = 0;
            while j < k
                invariant
                    0 <= j <= k,
                    sum == start_index(j, n, k),
                decreases k - j
            {
                sum = sum + chunk_size(j, n, k);
                j = j + 1;
            }
            assert(sum == n) by {
                let q = n / k;
                let r = n % k;
                assert(n == q * k + r);
                assert(sum == r * ((n + k - 1) / k) + (k - r) * (n / k));
                assert((n + k - 1) / k == q + if r > 0 { 1 } else { 0 });
            }
        }
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
    /* code modified by LLM (iteration 5): Fixed syntax error in proof block */
    let n = v.len();
    let mut result: Vec<Vec<i8>> = Vec::new();
    let mut current_pos: usize = 0;
    let mut i: usize = 0;
    
    while i < k
        invariant
            result.len() == i,
            current_pos == start_index(i as int, n as int, k as int) as usize,
            current_pos <= n,
            forall|j: int| 0 <= j < i as int ==> #[trigger] result[j].len() == chunk_size(j, n as int, k as int),
            forall|j: int, idx: int| 0 <= j < i as int && 0 <= idx < result[j].len() ==> 
                #[trigger] result[j][idx] == v[start_index(j, n as int, k as int) + idx],
        decreases k - i
    {
        proof {
            lemma_start_index_bounds(i as int, n as int, k as int);
            lemma_start_index_bounds((i + 1) as int, n as int, k as int);
            lemma_chunk_size_bounds(i as int, n as int, k as int);
            if i < k - 1 {
                lemma_start_index_plus_chunk_size(i as int, n as int, k as int);
            } else {
                lemma_chunk_sizes_sum_to_n(n as int, k as int);
            }
        }
        
        let chunk_len: usize = if i < (n % k) {
            if n >= k - 1 {
                (n + k - 1) / k
            } else {
                1
            }
        } else {
            n / k
        };
        
        assert(chunk_len == chunk_size(i as int, n as int, k as int) as usize);
        
        let mut chunk: Vec<i8> = Vec::new();
        let mut j: usize = 0;
        
        while j < chunk_len
            invariant
                chunk.len() == j,
                j <= chunk_len,
                chunk_len == chunk_size(i as int, n as int, k as int) as usize,
                current_pos as int + j as int <= n as int,
                current_pos as int + chunk_len as int <= n as int,
                forall|idx: int| 0 <= idx < j as int ==> #[trigger] chunk[idx] == v[current_pos as int + idx],
            decreases chunk_len - j
        {
            proof {
                assert(current_pos as int + j as int < n as int);
            }
            chunk.push(v[current_pos + j]);
            j = j + 1;
        }
        
        assert(chunk.len() == chunk_size(i as int, n as int, k as int));
        assert(forall|idx: int| 0 <= idx < chunk.len() ==> chunk[idx] == v[start_index(i as int, n as int, k as int) + idx]);
        
        result.push(chunk);
        current_pos = current_pos + chunk_len;
        i = i + 1;
    }
    
    proof {
        lemma_chunk_sizes_sum_to_n(n as int, k as int);
        assert(current_pos == n);
    }
    
    result
}
// </vc-code>


}
fn main() {}