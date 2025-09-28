// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): arithmetic lemmas to relate i < n - k to bounds i < n and i + k < n */
proof fn add_lt_from_sub(n: usize, i: usize, k: usize)
    requires
        i < n - k,
    ensures
        i + k < n,
{
    assert(i + k < n);
}

/* helper modified by LLM (iteration 2): consequence i < n from i < n - k */
proof fn lt_from_sub(n: usize, i: usize, k: usize)
    requires
        i < n - k,
    ensures
        i < n,
{
    assert(i < n);
}
// </vc-helpers>

// <vc-spec>
/* Matrix type represented as a 2D vector */
type Matrix<T> = Vec<Vec<T>>;

fn diagonal(arr: Matrix<i8>, k: i8) -> (result: Vec<i8>)
    requires 
        arr.len() > 0,
        arr.len() == arr[0].len(), /* square matrix */
        forall|i: int| 0 <= i < arr.len() ==> arr[i].len() == arr.len(),
        -(arr.len() as i8) < k && k < (arr.len() as i8),
    ensures
        if k > 0 {
            result.len() == arr.len() - (k as usize) &&
            forall|i: int| 0 <= i < result.len() ==> result[i] == arr[i][i + (k as usize)]
        } else {
            result.len() == arr.len() + ((-k) as usize) &&
            forall|i: int| 0 <= i < result.len() ==> result[i] == arr[i + ((-k) as usize)][i]
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fix invariant indexing types by using int indexing for specs */
    let n: usize = arr.len();
    let mut res: Vec<i8> = Vec::new();

    if k > 0 {
        let ku: usize = k as usize;
        let target_len: usize = n - ku;
        let mut i: usize = 0;
        while i < target_len
            invariant
                arr.len() == n,
                n > 0,
                arr.len() == arr[0].len(),
                forall|t: int| 0 <= t < n ==> arr[t].len() == n,
                k > 0,
                ku == k as usize,
                target_len == n - ku,
                i <= target_len,
                res.len() == i,
                forall|j: int| 0 <= j < i ==> res@[j] == arr[j][j + (ku as int)],
            decreases target_len - i
        {
            proof { lt_from_sub(n, i, ku); }
            proof { add_lt_from_sub(n, i, ku); }
            let v = arr[i][i + ku];
            res.push(v);
            i = i + 1;
        }
        res
    } else {
        let ku: usize = (-k) as usize;
        let target_len: usize = n - ku;
        let mut i: usize = 0;
        while i < target_len
            invariant
                arr.len() == n,
                n > 0,
                arr.len() == arr[0].len(),
                forall|t: int| 0 <= t < n ==> arr[t].len() == n,
                k <= 0,
                ku == (-k) as usize,
                target_len == n - ku,
                i <= target_len,
                res.len() == i,
                forall|j: int| 0 <= j < i ==> res@[j] == arr[j + (ku as int)][j],
            decreases target_len - i
        {
            proof { lt_from_sub(n, i, ku); }
            proof { add_lt_from_sub(n, i, ku); }
            let v = arr[i + ku][i];
            res.push(v);
            i = i + 1;
        }
        res
    }
}
// </vc-code>


}
fn main() {}