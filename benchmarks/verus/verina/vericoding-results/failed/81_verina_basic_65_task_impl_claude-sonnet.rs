// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed arithmetic assertions and added proper bounds */
spec fn is_perfect_square(n: usize, root: usize) -> bool {
    root * root <= n && n < (root + 1) * (root + 1)
}

proof fn square_properties(a: usize, b: usize)
    requires a <= b
    ensures a * a <= b * b
{
    if a == b {
        assert(a * a == b * b);
    } else {
        assert(a < b);
        assert(a * a <= a * a + a * (b - a));
        assert(a * a + a * (b - a) == a * b);
        assert(a * b <= b * b);
    }
}

proof fn increment_square_lemma(k: usize)
    ensures (k + 1) * (k + 1) == k * k + 2 * k + 1
{
    calc! {
        (==)
        (k + 1) * (k + 1);
        (k + 1) * k + (k + 1) * 1;
        k * k + 1 * k + (k + 1) * 1;
        k * k + k + k + 1;
        k * k + 2 * k + 1;
    }
}
// </vc-helpers>

// <vc-spec>
fn square_root(n: usize) -> (result: usize)
    ensures
        result * result <= n,
        n < (result + 1) * (result + 1),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed overflow and invariant issues */
    if n == 0 {
        return 0;
    }
    
    let mut low = 0usize;
    let mut high = (n + 1).min(46341usize); // sqrt(2^32 - 1) ≈ 65535, but using safe bound
    
    while high - low > 1
        invariant
            low * low <= n,
            n < high * high,
            low < high
        decreases high - low
    {
        let mid = low + (high - low) / 2;
        
        assert(low < mid && mid < high);
        
        if mid * mid <= n {
            low = mid;
        } else {
            high = mid;
        }
    }
    
    low
}
// </vc-code>

}
fn main() {}