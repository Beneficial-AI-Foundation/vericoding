// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
proof fn lemma_mult_poly(a: Seq<f64>, b: Seq<f64>) -> (res: Seq<f64>)
    requires a.len() > 0, b.len() > 0
    ensures res.len() == a.len() + b.len() - 1
{
    let len_a = a.len();
    let len_b = b.len();
    let len_res = (len_a + len_b - 1) as nat;
    let mut res: Seq<f64> = Seq::new(len_res, |i| 0.0);
    for i in 0..len_a as int
        invariant 
            res.len() == len_res,
        decreases len_a - i as nat
    {
        for j in 0..len_b as int
            invariant
                res.len() == len_res,
            decreases len_b - j as nat
        {
            let term = a[i as nat] * b[j as nat];
            let idx = (i + j) as nat;
            res = res.update(idx, res[idx] + term);
        }
    }
    res
}

/* helper modified by LLM (iteration 5): Added `result_vec_insert_zeros` function. */
fn result_vec_insert_zeros(res: &mut Vec<f64>, start_index: usize, count: usize) {
    for _i in start_index..count {
        res.push(0.0);
    }
}
// </vc-helpers>

// <vc-spec>
fn hermepow(c: Vec<f64>, pow: usize, maxpower: usize) -> (result: Vec<f64>)
    requires 
        pow <= maxpower,
        maxpower <= 16,
        c.len() > 0,
    ensures

        pow == 0 ==> result.len() == 1 && result[0] == 1.0 && 
            (forall|i: int| #![trigger result[i]] 1 <= i < result.len() ==> result[i] == 0.0),
        pow == 1 ==> result.len() == c.len() &&
            (forall|i: int| #![trigger result[i]] 0 <= i < c.len() ==> result[i] == c[i]),

        pow >= 1 ==> result.len() == 1 + (c.len() - 1) * pow,

        true, // Highest coefficient exists (simplified)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected `c_seq` creation by ensuring `nat` is used for `Seq` size, fixed `result_vec_insert_zeros` function call missing in helpers, and ensure indices for `current_pow_poly` are `nat` when accessing elements. */
{
    let c_seq = Seq::new(c.len() as nat, |i: nat| c[i as usize]);

    if pow == 0 {
        let mut res = Vec::new();
        res.push(1.0);
        result_vec_insert_zeros(&mut res, 1, c.len());
        return res;
    } else if pow == 1 {
        let mut res = Vec::new();
        for x in c.iter() {
            res.push(*x);
        }
        return res;
    }

    let mut current_pow_poly = c_seq;
    let mut current_pow = 1;

    while current_pow < pow
        invariant
            current_pow >= 1,
            current_pow <= pow,
            current_pow_poly.len() == 1 + (c_seq.len() - 1) * current_pow as nat,
        decreases pow - current_pow
    {
        current_pow_poly = lemma_mult_poly(current_pow_poly, c_seq);
        current_pow = current_pow + 1;
    }

    let mut result_vec = Vec::new();
    for i in 0..current_pow_poly.len() {
        result_vec.push(current_pow_poly@[i as nat]);
    }
    result_vec
}
// </vc-code>

}
fn main() {}