// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

proof fn vec_add_proof_lemma(x1: Seq<i8>, x2: Seq<i8>, result: Seq<i8>)
    requires
        x1.len() == x2.len(),
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == x1[i] as int + x2[i] as int
    ensures
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == x1[i] as int + x2[i] as int
{
}

/* helper modified by LLM (iteration 5): Fixed type casting issues by using proper numeric limits */
fn vec_add_helper(a: i8, b: i8) -> (c: i8)
    ensures c as int == a as int + b as int
{
    let a_int: int = a as int;
    let b_int: int = b as int;
    let sum_i32 = a_int + b_int;
    
    if sum_i32 < (-128i32) as int {
        -128i8
    } else if sum_i32 > (127i32) as int {
        127i8
    } else {
        sum_i32 as i8
    }
}

// </vc-helpers>

// <vc-spec>
fn add(x1: Vec<i8>, x2: Vec<i8>) -> (result: Vec<i8>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] as int == x1[i] as int + x2[i] as int
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed compilation errors by using proper type casting */
    let mut result = Vec::new();
    let mut i: usize = 0;
    
    while i < x1.len()
        invariant
            result.len() == i,
            i <= x1.len(),
            forall|j: int| 0 <= j < i ==> result@[j] as int == x1@[j] as int + x2@[j] as int
        decreases x1.len() - i
    {
        let a_val = x1[i];
        let b_val = x2[i];
        let sum = vec_add_helper(a_val, b_val);
        result.push(sum);
        i = i + 1;
    }
    
    proof {
        vec_add_proof_lemma(x1@, x2@, result@);
    }
    
    result
}
// </vc-code>


}
fn main() {}