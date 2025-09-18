// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed compute_length function signature and added proper lemma */
fn compute_length(len: usize, pow: usize, maxpower: usize) -> usize 
    ensures 
        result == if len + (len - 1) * pow <= maxpower + 1 { len + (len - 1) * pow } else { maxpower + 1 }
{
    if len + (len - 1) * pow <= maxpower + 1 {
        len + (len - 1) * pow
    } else {
        maxpower + 1
    }
}

proof fn lemma_pow_zero(len: usize, maxpower: usize) 
    ensures 
        (if len + (len - 1) * 0 <= maxpower + 1 { len + (len - 1) * 0 } else { maxpower + 1 }) == 1
{
}

proof fn lemma_pow_one(len: usize, maxpower: usize) 
    ensures 
        len <= maxpower + 1 ==> (if len + (len - 1) * 1 <= maxpower + 1 { len + (len - 1) * 1 } else { maxpower + 1 }) == len
{
}
// </vc-helpers>

// <vc-spec>
fn hermpow(c: Vec<f64>, pow: usize, maxpower: usize) -> (result: Vec<f64>)
    requires 
        c.len() > 0,
        maxpower >= 0,
    ensures

        result.len() <= maxpower + 1,
        result.len() == if c.len() + (c.len() - 1) * pow <= maxpower + 1 {
            c.len() + (c.len() - 1) * pow
        } else {
            maxpower + 1
        },

        pow == 0 ==> result.len() == 1 && result[0] == 1.0,

        (pow == 1 && c.len() <= maxpower + 1) ==> (
            result.len() == c.len() &&
            forall|i: int| 0 <= i < c.len() ==> result[i] == c[i]
        ),

        ((exists|i: int| 0 <= i < c.len() && c[i] != 0.0) && pow > 0) ==> 
            exists|j: int| 0 <= j < result.len() && result[j] != 0.0,
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed result variable declaration and return */
{
    let result;
    
    if pow == 0 {
        proof { lemma_pow_zero(c.len(), maxpower); }
        let mut res = Vec::new();
        res.push(1.0);
        result = res;
    } else if pow == 1 {
        proof { lemma_pow_one(c.len(), maxpower); }
        if c.len() <= maxpower + 1 {
            result = c.clone();
        } else {
            let mut res = Vec::with_capacity(maxpower + 1);
            for i in 0..maxpower + 1 {
                res.push(c[i]);
            }
            result = res;
        }
    } else {
        let length = compute_length(c.len(), pow, maxpower);
        let mut current = c.clone();
        
        for _ in 1..pow {
            let mut temp = Vec::new();
            for i in 0..current.len() {
                for j in 0..c.len() {
                    if temp.len() < length {
                        temp.push(current[i] * c[j]);
                    }
                }
            }
            current = temp;
        }
        
        result = current;
    }
    
    result
}
// </vc-code>

}
fn main() {}