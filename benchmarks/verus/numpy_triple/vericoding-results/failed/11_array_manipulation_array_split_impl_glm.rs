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
    /* code modified by LLM (iteration 2): fixed int type usage in non-ghost code */
    let mut result = Vec::with_capacity(k);
    let mut start: usize = 0;
    let mut i: usize = 0;
    while i < k
        invariant
            0 <= i <= k,
            start as int == start_index(i as int, v.len() as int, k as int),
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> 
                #[trigger] result[j as usize].len() as int == chunk_size(j, v.len() as int, k as int) &&
                forall|l: int| 0 <= l < result[j as usize].len() as int ==> 
                    #[trigger] result[j as usize][l as usize] == v[start_index(j, v.len() as int, k as int) + l]
    {
        let size = if i < (v.len() % k) {
            (v.len() + k - 1) / k
        } else {
            v.len() / k
        };
        let chunk = v.subrange(start, start + size);
        result.push(chunk);
        start += size;
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}