// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

/* helper modified by LLM (iteration 5): added division by zero check for d and n */
fn safe_div(a: int, b: int) -> int
    requires b != 0
{
    a / b
}

/* helper modified by LLM (iteration 5): added helper for safe casting */
fn safe_cast_to_i8(val: int) -> i8
    requires -128 <= val <= 127
{
    val as i8
}

/* helper modified by LLM (iteration 5): added lemma for monotonicity */
proof fn lemma_div_monotonic(a: int, b: int, c: int, d: int)
    requires
        0 <= a <= b,
        c > 0,
        d > 0
    ensures
        a / (c * d) <= b / (c * d)
{
}

// </vc-helpers>

// <vc-spec>
fn numpy_rfftfreq(n: usize, d: i8) -> (result: Vec<i8>)
    requires 
        n > 0,
        d > 0,
    ensures
        result.len() == n / 2 + 1,
        result@[0] == 0,
        forall|i: int| 0 <= i < result.len() ==> result@[i] == i / ((d as int) * (n as int)),
        result@[(n / 2) as int] == (n / 2) as int / ((d as int) * (n as int)),
        forall|i: int, j: int| 0 <= i <= j < result.len() ==> result@[i] <= result@[j],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): moved int casts to ghost context */
    let mut result = Vec::new();
    let mut i: usize = 0;
    let target_len = n / 2 + 1;
    
    ghost let denominator = (d as int) * (n as int);
    
    while i < target_len
        invariant
            i <= target_len,
            result.len() == i,
            forall|k: int| 0 <= k < i ==> result@[k] == (k as int) / denominator,
            denominator > 0
        decreases target_len - i
    {
        proof {
            let freq_calc = (i as int) / denominator;
            assert(freq_calc >= 0);
            assert(freq_calc <= (target_len as int) / denominator);
            assert(freq_calc <= 127); // within i8 range
        }
        ghost let freq_val = (i as int) / denominator;
        let freq = safe_cast_to_i8(freq_val);
        result.push(freq);
        i += 1;
    }
    
    proof {
        assert(result@[0] == 0);
        lemma_div_monotonic(0, (n / 2) as int, d as int, n as int);
    }
    
    result
}
// </vc-code>


}
fn main() {}