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
{
proof fn start_index_next(i: int, n: int, k: int)
    requires 0 <= i && i + 1 <= k,
    ensures start_index(i + 1, n, k) == start_index(i, n, k) + chunk_size(i, n, k),
    decreases k - i
{
    // Follows directly from the recursive definition of start_index
    if i > 0 {
        start_index_next(i - 1, n, k);
    }
}

proof fn start_index_prefix_sum(i: int, n: int, k: int)
    requires 0 <= i && i <= k,
    ensures start_index(i, n, k) == (if i <= 0 { 0 } else { start_index(i - 1, n, k) + chunk_size(i - 1, n, k) }),
    decreases i
{
    // Simple induction on i using the definition of start_index
    if i > 0 {
        start_index_prefix_sum(i - 1, n, k);
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
    // impl-start
    let mut result: Vec<Vec<i8>> = Vec::new();
    let n_usize: usize = v.len();
    let n_int: int = n_usize as int;
    let k_usize: usize = k;
    let k_int: int = k_usize as int;

    let mut i: usize = 0;
    while i < k_usize
        invariant
            result.len() == i,
            i <= k_usize,
        decreases k_usize - i
    {
        let i_int: int = i as int;
        let sz_int: int = chunk_size(i_int, n_int, k_int);
        let sz: usize = (sz_int) as usize;
        let start_int: int = start_index(i_int, n_int, k_int);
        let start: usize = start_int as usize;

        let mut sub: Vec<i8> = Vec::new();
        let mut j: usize = 0;
        while j < sz
            invariant
                sub.len() == j,
                j <= sz,
            decreases sz - j
        {
            let pos: usize = start + j;
            sub.push(v[pos]);
            j += 1;
        }

        result.push(sub);
        i += 1;
    }

    result
    // impl-end
}

// </vc-code>


}
fn main() {}