// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): safe vec get */
fn vec_get(arr: &Vec<i32>, k: usize) -> i32
    requires
        k < arr.len(),
{
    arr[k]
}
// </vc-helpers>

// <vc-spec>
fn swap(arr: &Vec<i32>, i: usize, j: usize) -> (result: Vec<i32>)
    requires
        i < arr.len(),
        j < arr.len(),
    ensures
        result.len() == arr.len(),
        result[i as int] == arr[j as int],
        result[j as int] == arr[i as int],
        forall|k: int| 0 <= k < arr.len() && k != i && k != j ==> result[k] == arr[k],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): implement swap by building new vector with invariant relating prefix to arr */
    let n = arr.len();
    let mut res: Vec<i32> = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant
            k <= n,
            res.len() == k,
            n == arr.len(),
            i < n,
            j < n,
            forall|p: int| 0 <= p < k as int ==> (
                if p == i as int {
                    res[p as int] == arr[j as int]
                } else if p == j as int {
                    res[p as int] == arr[i as int]
                } else {
                    res[p as int] == arr[p as int]
                }
            ),
        decreases n - k
    {
        if k == i {
            res.push(arr[j]);
        } else if k == j {
            res.push(arr[i]);
        } else {
            res.push(arr[k]);
        }
        k += 1;
    }
    res
}
// </vc-code>

}
fn main() {}