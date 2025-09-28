// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix result variable usage and ensure proper type conversions */
fn calculate_freq(i: int, n: int, d: int) -> i8
    requires
        d > 0,
        n > 0,
        0 <= i <= n / 2,
    ensures
        result == i / (d * n),
{
    (i / (d * n)) as i8
}

proof fn monotonic_proof(i: int, j: int, n: int, d: int)
    requires
        0 <= i <= j <= n / 2,
        d > 0,
        n > 0,
    ensures
        calculate_freq(i, n, d) <= calculate_freq(j, n, d),
{
    assert(i / (d * n) <= j / (d * n));
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
/* code modified by LLM (iteration 5): Fix result variable usage and ensure proper type conversions */
{
    let mut result = Vec::empty();
    let len = (n / 2) + 1;
    
    let n_int = n as int;
    let d_int = d as int;
    
    let mut i: usize = 0;
    while i < len
        invariant
            result.len() == i as int,
            forall|k: int| 0 <= k < i as int ==> result@[k] == calculate_freq(k, n_int, d_int),
            i <= len,
        decreases len - i,
    {
        let freq = calculate_freq(i as int, n_int, d_int);
        result.push(freq);
        i = i + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}