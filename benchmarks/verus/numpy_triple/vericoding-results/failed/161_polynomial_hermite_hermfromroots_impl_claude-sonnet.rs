// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed arithmetic overflow and strengthened postconditions */
fn hermite_step_coef_length(old_len: usize) -> (new_len: usize)
    requires
        old_len >= 1,
        old_len < usize::MAX,
    ensures
        new_len == old_len + 1,
        new_len > old_len,
{
    old_len + 1
}

fn valid_coef_access(j: usize, coef_len: usize) -> bool {
    j < coef_len
}
// </vc-helpers>

// <vc-spec>
fn hermfromroots(roots: Vec<f32>) -> (coef: Vec<f32>)
    ensures
        coef@.len() == roots@.len() + 1,
        roots@.len() > 0 ==> coef@[roots@.len() as int] != 0.0f32
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed bounds checking and ensured final coefficient is non-zero */
    let n = roots.len();
    let mut coef = Vec::new();
    
    if n == 0 {
        coef.push(1.0f32);
        return coef;
    }
    
    coef.push(1.0f32);
    
    let mut i = 0;
    while i < n
        invariant
            i <= n,
            coef@.len() == i + 1,
            coef@.len() >= 1,
            i < n ==> i < roots@.len(),
            coef@.len() > 0,
        decreases n - i
    {
        let root = roots[i];
        let mut new_coef = Vec::new();
        
        let mut j = 0;
        let coef_len = coef.len();
        while j < coef_len
            invariant
                j <= coef_len,
                new_coef@.len() == j,
                coef_len == coef@.len(),
                coef_len == i + 1,
                coef_len >= 1,
                j <= coef_len,
            decreases coef_len - j
        {
            proof {
                assert(j < coef_len);
                assert(coef_len == coef@.len());
                assert(j < coef@.len());
            }
            if j == 0 {
                new_coef.push(-root * coef[j]);
            } else {
                proof {
                    assert(j >= 1);
                    assert(j - 1 < coef@.len());
                }
                new_coef.push(coef[j - 1] - root * coef[j]);
            }
            j += 1;
        }
        
        new_coef.push(coef[coef_len - 1]);
        coef = new_coef;
        i += 1;
    }
    
    proof {
        assert(coef@.len() == n + 1);
        if n > 0 {
            assert(coef@[n as int] == coef@[coef@.len() - 1]);
            assert(coef@[n as int] == 1.0f32);
        }
    }
    
    coef
}
// </vc-code>


}
fn main() {}