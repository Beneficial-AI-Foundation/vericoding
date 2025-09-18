// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_all_zero(c: Seq<f64>) -> bool { forall |i: int| 0 <= i < c.len() ==> c[i] == 0.0 }
/* helper modified by LLM (iteration 4): kept spec function from previous iteration to assist in verifying postcondition */
/* helper modified by LLM (iteration 5): no modifications, carried over from previous iteration */
// </vc-helpers>

// <vc-spec>
fn hermemul(c1: Vec<f64>, c2: Vec<f64>) -> (result: Vec<f64>)
    requires 
        c1.len() > 0,
        c2.len() > 0,
    ensures
        result.len() == c1.len() + c2.len() - 1,
        (forall|i: int| 0 <= i < c1.len() ==> c1[i] == 0.0) || 
        (forall|j: int| 0 <= j < c2.len() ==> c2[j] == 0.0) 
        ==> (forall|k: int| 0 <= k < result.len() ==> result[k] == 0.0)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed typos in Vec type and variable name));
    let length: int = c1@.len() as int + c2.len() as int - (>
    let mut result: Seq<f64> = Seq::empty();
    let mut reg: int = 0;
    while reg < length {
        invariant 0 <= reg && reg <= length;
        invariant result.len() == reg as nat;
        result = result.push(0.0);
        reg = reg + 1;
    }
    assert(result.len() == length as nat);
    let mut i: int = 0;
    while i < c1.len() as int {
        invariant 0 <= i && i <= c1.len() as int;
        invariant result.len() == length as nat;
        let mut j: int = 0;
        while j < c2.len() as int {
            invariant 0 <= j && j <= c2.len() as int;
            let k = i + j;
            if k < length {
                result = result.update(k as nat, result[k as nat] + c1[i as usize] * c2[j as usize]);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    let mut result_vec: Vec<f64> = Vec::new();
    let mut idx: int = 0;
    while idx < length {
        invariant 0 <= idx && idx <= length;
        result_vec.push(result[idx as nat]);
        idx = idx + 1;
    }
    result_vec
}
// </vc-code>

}
fn main() {}