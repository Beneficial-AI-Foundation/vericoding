// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): prove monotonicity of int cast for usize ordering */
proof fn lemma_usize_le_implies_int(u: usize, v: usize)
    ensures
        u <= v ==> (u as int) <= (v as int),
{
    if u <= v {
        assert((u as int) <= (v as int));
    }
}

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
    /* code modified by LLM (iteration 4): implement concatenation with strengthened invariants and explicit bounds assertions */
    let n: usize = top_left.len();
    let mut result: Vec<f32> = Vec::new();

    // Copy top_left
    let mut i: usize = 0;
    while i < n
        invariant
            result.len() == i,
            i <= n,
            0 <= i as int,
            i as int <= n as int,
            n == top_left.len(),
            forall|k: int| 0 <= k < i as int ==> result[k] == top_left[k],
        decreases n as int - i as int
    {
        assert(i < n);
        assert(n == top_left.len());
        assert(i < top_left.len());
        let val = top_left[i];
        result.push(val);
        i += 1;
    }

    // Copy top_right
    let mut j: usize = 0;
    while j < n
        invariant
            result.len() == n + j,
            j <= n,
            0 <= j as int,
            j as int <= n as int,
            n == top_left.len(),
            n == top_right.len(),
            forall|k: int| 0 <= k < n as int ==> result[k] == top_left[k],
            forall|k: int| 0 <= k < j as int ==> result[n as int + k] == top_right[k],
        decreases n as int - j as int
    {
        assert(j < n);
        assert(n == top_right.len());
        assert(j < top_right.len());
        let val = top_right[j];
        result.push(val);
        j += 1;
    }

    // Copy bottom_left
    let mut k: usize = 0;
    while k < n
        invariant
            result.len() == 2 * n + k,
            k <= n,
            0 <= k as int,
            k as int <= n as int,
            n == top_left.len(),
            n == top_right.len(),
            n == bottom_left.len(),
            forall|t: int| 0 <= t < n as int ==> result[t] == top_left[t],
            forall|t: int| 0 <= t < n as int ==> result[n as int + t] == top_right[t],
            forall|t: int| 0 <= t < k as int ==> result[(2 * n) as int + t] == bottom_left[t],
        decreases n as int - k as int
    {
        assert(k < n);
        assert(n == bottom_left.len());
        assert(k < bottom_left.len());
        let val = bottom_left[k];
        result.push(val);
        k += 1;
    }

    // Copy bottom_right
    let mut m: usize = 0;
    while m < n
        invariant
            result.len() == 3 * n + m,
            m <= n,
            0 <= m as int,
            m as int <= n as int,
            n == top_left.len(),
            n == top_right.len(),
            n == bottom_left.len(),
            n == bottom_right.len(),
            forall|t: int| 0 <= t < n as int ==> result[t] == top_left[t],
            forall|t: int| 0 <= t < n as int ==> result[n as int + t] == top_right[t],
            forall|t: int| 0 <= t < n as int ==> result[(2 * n) as int + t] == bottom_left[t],
            forall|t: int| 0 <= t < m as int ==> result[(3 * n) as int + t] == bottom_right[t],
        decreases n as int - m as int
    {
        assert(m < n);
        assert(n == bottom_right.len());
        assert(m < bottom_right.len());
        let val = bottom_right[m];
        result.push(val);
        m += 1;
    }

    result
}
// </vc-code>

}
fn main() {}