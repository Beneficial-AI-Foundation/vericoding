// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): simple spec helpers for ranges and min */
spec fn min_int(a: int, b: int) -> int { if a <= b { a } else { b } }
spec fn in_range(i: int, n: int) -> bool { 0 <= i && i < n }
// </vc-helpers>

// <vc-spec>
fn bmat(top_left: Vec<f32>, top_right: Vec<f32>, bottom_left: Vec<f32>, bottom_right: Vec<f32>) -> (result: Vec<f32>)
    requires 
        top_left.len() == top_right.len(),
        top_left.len() == bottom_left.len(),
        top_left.len() == bottom_right.len(),
    ensures
        result.len() == 4 * top_left.len(),
        forall|i: int| 0 <= i < top_left.len() ==> result[i] == top_left[i],
        forall|i: int| 0 <= i < top_right.len() ==> result[i + top_left.len()] == top_right[i],
        forall|i: int| 0 <= i < bottom_left.len() ==> result[i + 2 * top_left.len()] == bottom_left[i],
        forall|i: int| 0 <= i < bottom_right.len() ==> result[i + 3 * top_left.len()] == bottom_right[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): build concatenated vector with explicit length invariants and bounded quantified properties */
    let n = top_left.len();
    let mut res: Vec<f32> = Vec::new();

    let mut i: usize = 0;
    while i < n
        invariant
            res.len() == i,
            i <= n,
            top_left.len() == n,
            top_right.len() == n,
            bottom_left.len() == n,
            bottom_right.len() == n,
            forall|j: int| 0 <= j < i as int && j < top_left.len() ==> res@[j] == top_left@[j]
        decreases n - i
    {
        let v = top_left[i];
        res.push(v);
        i += 1;
    }

    let mut j: usize = 0;
    while j < n
        invariant
            res.len() == n + j,
            j <= n,
            top_left.len() == n,
            top_right.len() == n,
            bottom_left.len() == n,
            bottom_right.len() == n,
            forall|k: int| 0 <= k < top_left.len() ==> res@[k] == top_left@[k],
            forall|k: int| 0 <= k < j as int && k < top_right.len() ==> res@[n as int + k] == top_right@[k]
        decreases n - j
    {
        let v = top_right[j];
        res.push(v);
        j += 1;
    }

    let mut k: usize = 0;
    while k < n
        invariant
            res.len() == 2 * n + k,
            k <= n,
            top_left.len() == n,
            top_right.len() == n,
            bottom_left.len() == n,
            bottom_right.len() == n,
            forall|t: int| 0 <= t < top_left.len() ==> res@[t] == top_left@[t],
            forall|t: int| 0 <= t < top_right.len() ==> res@[n as int + t] == top_right@[t],
            forall|t: int| 0 <= t < k as int && t < bottom_left.len() ==> res@[2 * (n as int) + t] == bottom_left@[t]
        decreases n - k
    {
        let v = bottom_left[k];
        res.push(v);
        k += 1;
    }

    let mut r: usize = 0;
    while r < n
        invariant
            res.len() == 3 * n + r,
            r <= n,
            top_left.len() == n,
            top_right.len() == n,
            bottom_left.len() == n,
            bottom_right.len() == n,
            forall|t: int| 0 <= t < top_left.len() ==> res@[t] == top_left@[t],
            forall|t: int| 0 <= t < top_right.len() ==> res@[n as int + t] == top_right@[t],
            forall|t: int| 0 <= t < bottom_left.len() ==> res@[2 * (n as int) + t] == bottom_left@[t],
            forall|t: int| 0 <= t < r as int && t < bottom_right.len() ==> res@[3 * (n as int) + t] == bottom_right@[t]
        decreases n - r
    {
        let v = bottom_right[r];
        res.push(v);
        r += 1;
    }

    res
}
// </vc-code>

}
fn main() {}