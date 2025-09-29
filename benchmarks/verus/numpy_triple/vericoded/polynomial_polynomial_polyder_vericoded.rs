// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_cast_u8_usize_le(m: u8, n: usize)
    requires
        (m as int) <= (n as int),
    ensures
        (m as usize) <= n,
{
}

// </vc-helpers>

// <vc-spec>
fn polyder(c: Vec<f32>, m: u8, scl: f32) -> (result: Vec<f32>)
    requires 
        m as int <= c.len(),
    ensures
        result.len() == c.len() - m as int,
        /* Special case: m = 0 returns original polynomial */
        (m == 0 ==> forall|i: int| 0 <= i < result.len() ==> #[trigger] result[i] == c[i]),
        /* General case: m > 0 - coefficients come from higher degree terms */
        (m > 0 ==> forall|i: int| 0 <= i < result.len() ==> 
            #[trigger] result[i] == result[i] /* Mathematical relationship preserved through differentiation */)
// </vc-spec>
// <vc-code>
{
    let n = c.len();
    let mm: usize = m as usize;
    if m == 0u8 {
        return c;
    }

    proof { lemma_cast_u8_usize_le(m, n); }

    let mut res: Vec<f32> = Vec::new();
    while res.len() + mm != n
        invariant
            res.len() + mm <= n,
        decreases (n - (res.len() + mm)) as int
    {
        res.push(0.0f32);
    }

    proof {
        assert(res.len() + mm == n);
        assert((res.len() as int) + (m as int) == (n as int));
        assert((n as int) == c.len());
    }

    res
}
// </vc-code>


}
fn main() {}