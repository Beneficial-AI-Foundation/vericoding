// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn hermepow(c: Vec<f64>, pow: u8, maxpower: u8) -> (result: Vec<f64>)
    requires 
        pow <= maxpower,
        maxpower <= 16,
        c.len() > 0,
    ensures

        pow == 0 ==> result.len() == 1 && result[0] == 1.0 && 
            (forall|i: int| 1 <= i < result.len() ==> result[i] == 0.0),
        pow == 1 ==> result.len() == c.len() &&
            (forall|i: int| 0 <= i < c.len() ==> result[i] == c[i]),

        pow as int >= 1 ==> result.len() == 1 + (c.len() - 1) * pow as int,

        pow as int >= 1 && c.len() > 0 ==> result.len() > 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Replaced `finite_seq_core_seq()` with `@` for sequence indexing in assertions. This fixes Verus compilation errors about `finite_seq_core_seq` not being found on `Vec`. */
    let len_c = c.len();

    if pow == 0 {
        let mut result = Vec::new();
        result.push(1.0);
        proof {
            assert(result.len() == 1);
            assert(result[0] == 1.0);
        }
        return result;
    }

    if pow == 1 {
        let mut result = Vec::new();
        let mut i = 0;
        while i < len_c
            invariant
                0 <= i && i <= len_c,
                result.len() == i,
                forall|j: int| 0 <= j < i ==> result@[j] == c@[j],
        {
            result.push(c[i]);
            i = i + 1;
        }
        proof {
            assert(result.len() == len_c);
        }
        return result;
    }

    let mut prev_hermepow_vec = hermepow(c.clone(), (pow - 1) as u8, maxpower);
    let len_prev = prev_hermepow_vec.len();
    let mut result = Vec::new();
    result.resize(1 + (len_c - 1) * pow as usize, 0.0);

    let mut k = 0usize;
    while k < len_prev
        invariant
            0 <= k && k <= len_prev,
            len_c > 0,
            // pow as int >= 2, // Ghost code
            prev_hermepow_vec.len() == len_prev,
            result.len() == 1 + (len_c - 1) * pow as usize,
            forall|idx: int| 0 <= idx < result.len() ==> result@[idx].is_finite(),
    {
        let mut i = 0usize;
        while i < len_c
            invariant
                0 <= i && i <= len_c,
                0 <= k && k < len_prev,
                len_c > 0,
                // pow as int >= 2, // Ghost code
                prev_hermepow_vec.len() == len_prev,
                result.len() == 1 + (len_c - 1) * pow as usize,
                forall|idx: int| 0 <= idx < result.len() ==> result@[idx].is_finite(),
        {
            if k + i < result.len() {
                let sum = result[k + i] + prev_hermepow_vec[k] * c[i];
                result.set(k + i, sum);
            }
            i = i + 1;
        }
        k = k + 1;
    }

    proof {
        if pow >= 1 && len_c > 0 {
            assert(result.len() == 1 + (len_c - 1) * pow as usize);
        }
    }

    result
}
// </vc-code>

}
fn main() {}