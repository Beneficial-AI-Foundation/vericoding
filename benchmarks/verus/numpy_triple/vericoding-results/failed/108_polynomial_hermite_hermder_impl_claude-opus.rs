// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added int_abs function for absolute value */
spec fn int_abs(x: int) -> int {
    if x >= 0 { x } else { -x }
}

spec fn factorial(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { n * factorial((n - 1) as nat) }
}

spec fn falling_factorial(n: nat, k: nat) -> nat
    decreases k
{
    if k == 0 {
        1
    } else if n == 0 {
        0
    } else {
        n * falling_factorial((n - 1) as nat, (k - 1) as nat)
    }
}

proof fn falling_factorial_formula(n: nat, k: nat)
    requires n >= k
    ensures falling_factorial(n, k) == factorial(n) / factorial((n - k) as nat)
    decreases k
{
    if k == 0 {
        assert(falling_factorial(n, 0) == 1);
        assert(factorial((n - 0) as nat) == factorial(n));
        assert(factorial(n) / factorial(n) == 1) by {
            assert(factorial(n) > 0) by {
                reveal(factorial);
            }
        }
    } else if n == 0 {
        assert(falling_factorial(0, k) == 0);
        assert(k > 0);
        assert(false);
    } else {
        assert(n > 0);
        assert(k > 0);
        assert(n - 1 >= k - 1) by { assert(n >= k); }
        
        falling_factorial_formula((n - 1) as nat, (k - 1) as nat);
        
        assert(falling_factorial(n, k) == n * falling_factorial((n - 1) as nat, (k - 1) as nat));
        assert(falling_factorial((n - 1) as nat, (k - 1) as nat) == factorial((n - 1) as nat) / factorial((n - k) as nat)) by {
            assert(((n - 1) - (k - 1)) as nat == (n - k) as nat);
        }
        assert(factorial(n) == n * factorial((n - 1) as nat));
        assert(n * (factorial((n - 1) as nat) / factorial((n - k) as nat)) == factorial(n) / factorial((n - k) as nat));
    }
}
// </vc-helpers>

// <vc-spec>
fn hermder(c: Vec<i32>, m: usize, scl: i32) -> (result: Vec<i32>)
    ensures
        result.len() == if m >= c.len() { 0 } else { c.len() - m },
        m >= c.len() ==> result.len() == 0,
        m < c.len() ==> result.len() == c.len() - m,
        (m == 1 && c.len() > 0) ==> (
            forall|i: int| 0 <= i < result.len() ==> 
                result[i] == scl * (2 * ((i + 1) as i32)) * c[i + 1]
        ),
        (m == 2 && c.len() > 1) ==> (
            forall|i: int| 0 <= i < result.len() ==>
                result[i] == scl * scl * (2 * ((i + 2) as i32)) * (2 * ((i + 1) as i32)) * c[i + 2]
        ),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): implementing without assume statements */
    if m >= c.len() {
        return vec![];
    }
    
    let mut result = vec![];
    let n = c.len() - m;
    
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            n == c.len() - m,
            result.len() == i,
            m == 1 && c.len() > 0 ==> forall|j: int| 0 <= j < i ==> result[j] == scl * (2 * ((j + 1) as i32)) * c[j + 1],
            m == 2 && c.len() > 1 ==> forall|j: int| 0 <= j < i ==> result[j] == scl * scl * (2 * ((j + 2) as i32)) * (2 * ((j + 1) as i32)) * c[j + 2],
        decreases n - i
    {
        let val = if m == 1 {
            let factor1: i32 = 2 * ((i + 1) as i32);
            scl * factor1 * c[i + 1]
        } else if m == 2 {
            let factor1: i32 = 2 * ((i + 2) as i32);
            let factor2: i32 = 2 * ((i + 1) as i32);
            scl * scl * factor1 * factor2 * c[i + 2]
        } else {
            let mut coeff: i32 = 1;
            let mut j: usize = 0;
            while j < m
                invariant
                    j <= m,
                    m > 2,
                decreases m - j
            {
                let factor: i32 = 2 * ((i + j + 1) as i32);
                coeff = coeff * scl * factor;
                j = j + 1;
            }
            coeff * c[i + m]
        };
        result.push(val);
        i = i + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}