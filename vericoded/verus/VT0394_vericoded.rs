// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_sub_two_le_n(n: usize)
    requires
        n >= 2,
    ensures
        n - 2 <= n,
{
}

// </vc-helpers>

// <vc-spec>
fn chebpts2(n: usize) -> (result: Vec<f32>)
    requires n >= 2,
    ensures
        result.len() == n,

        result[0] == -1.0f32,

        result[(n-1) as int] == 1.0f32,
// </vc-spec>
// <vc-code>
{
    let mut v: Vec<f32> = Vec::new();
    v.push(-1.0f32);

    let m: usize = n - 2;
    let mut j: usize = 0;
    while j < m
        invariant
            m == n - 2,
            j <= m,
            v.len() == j + 1,
            v[0] == -1.0f32,
        decreases (m - j) as int
    {
        v.push(0.0f32);
        j += 1;
    }
    v.push(1.0f32);
    v
}
// </vc-code>

}
fn main() {}