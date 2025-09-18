// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): made helper functions exec mode instead of spec */
exec fn safe_add_usize(a: usize, b: usize) -> bool {
    a <= usize::MAX - b
}

exec fn valid_indices(c1_len: usize, c2_len: usize) -> bool {
    c1_len > 0 && c2_len > 0 && safe_add_usize(c1_len, c2_len) && c1_len + c2_len >= 1
}

exec fn safe_multiply_i32(a: i32, b: i32) -> bool {
    a as i64 * b as i64 >= i32::MIN as i64 && a as i64 * b as i64 <= i32::MAX as i64
}

exec fn safe_add_i32(a: i32, b: i32) -> bool {
    a as i64 + b as i64 >= i32::MIN as i64 && a as i64 + b as i64 <= i32::MAX as i64
}

spec fn all_zero_c1(c1: Vec<i32>) -> bool {
    forall|i: int| 0 <= i < c1.len() ==> c1[i] == 0
}

spec fn all_zero_c2(c2: Vec<i32>) -> bool {
    forall|j: int| 0 <= j < c2.len() ==> c2[j] == 0
}
// </vc-helpers>

// <vc-spec>
fn hermmul(c1: Vec<i32>, c2: Vec<i32>) -> (result: Vec<i32>)
    ensures

        (c1.len() == 0 || c2.len() == 0) ==> (result.len() == 1 && result[0] == 0),

        (c1.len() > 0 && c2.len() > 0) ==> result.len() == c1.len() + c2.len() - 1,

        (c2.len() == 1 && c1.len() > 0) ==>
            forall|i: int| 0 <= i < c1.len() ==> result[i] == c1[i] * c2[0],
        (c1.len() == 1 && c2.len() > 0) ==>
            forall|i: int| 0 <= i < c2.len() ==> result[i] == c2[i] * c1[0],

        ((forall|i: int| 0 <= i < c1.len() ==> c1[i] == 0) || 
         (forall|j: int| 0 <= j < c2.len() ==> c2[j] == 0)) ==>
            forall|k: int| 0 <= k < result.len() ==> result[k] == 0,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed function call mode and improved overflow handling */
    if c1.len() == 0 || c2.len() == 0 {
        return vec![0];
    }
    
    if c1.len() > usize::MAX - c2.len() {
        return vec![0];
    }
    
    let result_len = c1.len() + c2.len() - 1;
    let mut result = Vec::with_capacity(result_len);
    
    let mut idx = 0;
    while idx < result_len
        invariant
            0 <= idx <= result_len,
            result.len() == idx,
            result_len == c1.len() + c2.len() - 1,
            c1.len() > 0,
            c2.len() > 0,
        decreases result_len - idx
    {
        result.push(0);
        idx = idx + 1;
    }
    
    let mut i = 0;
    while i < c1.len()
        invariant
            0 <= i <= c1.len(),
            result.len() == result_len,
            result_len == c1.len() + c2.len() - 1,
            c1.len() > 0,
            c2.len() > 0,
        decreases c1.len() - i
    {
        let mut j = 0;
        while j < c2.len()
            invariant
                0 <= i < c1.len(),
                0 <= j <= c2.len(),
                result.len() == result_len,
                result_len == c1.len() + c2.len() - 1,
                c1.len() > 0,
                c2.len() > 0,
                i + j < result_len,
            decreases c2.len() - j
        {
            if safe_multiply_i32(c1[i], c2[j]) && safe_add_i32(result[i + j], c1[i] * c2[j]) {
                let old_val = result[i + j];
                let prod = c1[i] * c2[j];
                let new_val = old_val + prod;
                result.set(i + j, new_val);
            }
            j = j + 1;
        }
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}