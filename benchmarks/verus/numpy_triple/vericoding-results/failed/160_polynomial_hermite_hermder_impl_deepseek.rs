// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fix product function signature and remove exec code from helpers */
spec fn factorial(n: nat) -> nat
    decreases n,
{
    if n == 0 {
        1
    } else {
        n * factorial(n - 1)
    }
}

spec fn binomial(n: nat, k: nat) -> nat
    requires
        k <= n,
    decreases n,
{
    if k == 0 || k == n {
        1
    } else {
        binomial(n - 1, k - 1) + binomial(n - 1, k)
    }
}

spec fn hermite_derivative_coeff(m: nat, i: nat, scl: int, c_seq: Seq<i8>) -> int
    requires
        m as usize <= c_seq.len(),
        i < c_seq.len() - m as usize,
    decreases m,
{
    if m == 0 {
        c_seq[i as usize] as int
    } else {
        scl * (2 * (i + m)) * hermite_derivative_coeff(m - 1, i, scl, c_seq)
    }
}

proof fn hermite_derivative_coeff_special_case1(m: nat, scl: int, c_seq: Seq<i8>)
    requires
        m == 1 && c_seq.len() > 0,
{
    let mut i: int = 0;
    while i < c_seq.len() - 1
        invariant
            0 <= i <= c_seq.len() - 1,
            forall|j: int| 0 <= j < i ==> 
                hermite_derivative_coeff(1, j as nat, scl, c_seq) == scl * (2 * (j + 1)) * (c_seq[(j + 1) as usize] as int),
        decreases (c_seq.len() - 1) as int - i,
    {
        assert(hermite_derivative_coeff(1, i as nat, scl, c_seq) == scl * (2 * (i + 1)) * (c_seq[(i + 1) as usize] as int));
        i = i + 1;
    }
}

proof fn hermite_derivative_coeff_special_case2(m: nat, scl: int, c_seq: Seq<i8>)
    requires
        m == 2 && c_seq.len() > 1,
{
    let mut i: int = 0;
    while i < c_seq.len() - 2
        invariant
            0 <= i <= c_seq.len() - 2,
            forall|j: int| 0 <= j < i ==> 
                hermite_derivative_coeff(2, j as nat, scl, c_seq) == scl * scl * (2 * (j + 2)) * (2 * (j + 1)) * (c_seq[(j + 2) as usize] as int),
        decreases (c_seq.len() - 2) as int - i,
    {
        assert(hermite_derivative_coeff(2, i as nat, scl, c_seq) == scl * scl * (2 * (i + 2)) * (2 * (i + 1)) * (c_seq[(i + 2) as usize] as int));
        i = i + 1;
    }
}
// </vc-helpers>

// <vc-spec>
fn hermder(c: Vec<i8>, m: usize, scl: i8) -> (result: Vec<i8>)
    ensures
        result.len() == if m >= c.len() { 0 } else { c.len() - m },
        m >= c.len() ==> result.len() == 0,
        m < c.len() ==> result.len() == c.len() - m,
        (m == 1 && c.len() > 0) ==> (
            forall|i: int| 0 <= i < result.len() ==> 
                result[i] as int == (scl as int) * (2 * ((i + 1) as int)) * (c[i + 1] as int)
        ),
        (m == 2 && c.len() > 1) ==> (
            forall|i: int| 0 <= i < result.len() ==>
                result[i] as int == (scl as int) * (scl as int) * (2 * ((i + 2) as int)) * (2 * ((i + 1) as int)) * (c[i + 2] as int)
        ),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): simplify implementation using direct computation */
    if m >= c.len() {
        return Vec::new();
    }
    
    let result_len = c.len() - m;
    let mut result = Vec::<i8>::new();
    let mut i: usize = 0;
    
    while i < result_len
        invariant
            result.len() == i,
            result_len == c.len() - m,
            m < c.len(),
    {
        let mut coeff: i32 = scl as i32;
        let mut k: usize = 0;
        
        while k < m
            invariant
                k <= m,
                coeff == (scl as i32).pow(k as u32) * (2_i32.pow(k as u32)) * factorial(k as u32) as i32,
        {
            coeff = coeff * (2 * (i + k + 1) as i32);
            k = k + 1;
        }
        
        coeff = coeff * (c[i + m] as i32);
        
        let result_val = if coeff > 127 { 127 } else if coeff < -128 { -128 } else { coeff as i8 };
        result.push(result_val);
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}