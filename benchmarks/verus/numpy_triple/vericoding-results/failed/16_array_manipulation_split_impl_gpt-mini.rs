// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
{
    /* helper modified by LLM (iteration 5): compute chunk length (arr_len / k) */
    fn chunk_len(arr_len: usize, k: usize) -> (result: usize)
        requires
            k > 0,
        ensures
            result == arr_len / k,
    {
        arr_len / k
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
    /* code modified by LLM (iteration 5): implement split using chunk_len and correct int casts in invariants */
    let n: usize = chunk_len(arr.len(), k);
    let mut res: Vec<Vec<f32>> = Vec::new();
    let mut i: usize = 0;
    while i < k
        invariant
            res.len() == i,
            forall|ii: int, jj: int| 0 <= ii && ii < i as int && 0 <= jj && jj < n as int ==> res[ii as usize][jj as usize] == arr[(ii * (n as int)) + jj],
        decreases k - i
    {
        let mut inner: Vec<f32> = Vec::new();
        let mut j: usize = 0;
        while j < n
            invariant
                inner.len() == j,
                forall|jj: int| 0 <= jj && jj < j as int ==> inner[jj as usize] == arr[(i as int * n as int) + jj],
            decreases n - j
        {
            let idx: usize = i * n + j;
            let val: f32 = arr[idx];
            inner.push(val);
            j += 1;
        }
        res.push(inner);
        i += 1;
    }
    res
}
// </vc-code>

}
fn main() {}