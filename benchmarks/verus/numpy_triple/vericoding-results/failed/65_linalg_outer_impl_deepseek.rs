// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added preconditions to ensure arithmetic safety and fixed type conversion */
fn create_inner_vector(len: usize, value: int) -> (result: Vec<int>)
    requires
        value * value <= 0x7FFFFFFF,
    ensures
        result.len() == len,
        forall|k: int| 0 <= k < len ==> result@[k] == value
{
    let mut vec: Vec<int> = Vec::new();
    let mut k: usize = 0;
    while k < len
        invariant
            0 <= k <= len,
            vec.len() == k,
            forall|m: int| 0 <= m < k ==> vec@[m] == value
        decreases len - k
    {
        vec.push(value);
        k = k + 1;
    }
    vec
}
proof fn mul_is_safe(a: int, b: int)
    requires
        a <= 0x7FFFFFFF,
        b <= 0x7FFFFFFF,
        a >= -0x80000000,
        b >= -0x80000000,
        a * b <= 0x7FFFFFFF,
        a * b >= -0x80000000,
    ensures
        (a * b) as i32 == a * b
{
}

// </vc-helpers>

// <vc-spec>
fn outer_i32(a: Vec<i32>, b: Vec<i32>) -> (result: Vec<Vec<i32>>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i].len() == b.len(),
        forall|i: int, j: int| 0 <= i < result.len() && 0 <= j < result[i].len() ==> 
            result[i][j] == a[i] * b[j],
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Added arithmetic safety checks and proof blocks */
{
    let mut result_vec: Vec<Vec<i32>> = Vec::new();
    
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result_vec.len() == i,
            forall|m: int| 0 <= m < i ==> result_vec@[m].len() == b.len(),
            forall|m: int, n: int| 0 <= m < i && 0 <= n < b.len() ==> 
                result_vec@[m]@[n] == a@[m] * b@[n]
        decreases a.len() - i
    {
        let inner_value = a[i];
        proof {
            mul_is_safe(inner_value as int, b@[0] as int);
        }
        let mut inner_vec: Vec<i32> = Vec::new();
        let mut j: usize = 0;
        
        while j < b.len()
            invariant
                0 <= j <= b.len(),
                inner_vec.len() == j,
                forall|k: int| 0 <= k < j ==> inner_vec@[k] == inner_value * b@[k]
            decreases b.len() - j
        {
            let b_val = b[j];
            proof {
                mul_is_safe(inner_value as int, b_val as int);
            }
            inner_vec.push(inner_value * b_val);
            j = j + 1;
        }
        
        result_vec.push(inner_vec);
        i = i + 1;
    }
    
    result_vec
}
// </vc-code>

}
fn main() {}