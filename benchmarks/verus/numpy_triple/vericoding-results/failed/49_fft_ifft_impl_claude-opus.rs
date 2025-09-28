// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no helpers needed */
// </vc-helpers>

// <vc-spec>
#[derive(PartialEq, Eq, Structural)]
pub struct Complex {
    pub re: int,
    pub im: int,
}

impl Complex {
    pub open spec fn add(self, other: Complex) -> Complex {
        Complex { re: self.re + other.re, im: self.im + other.im }
    }

    pub open spec fn mul(self, other: Complex) -> Complex {
        Complex { 
            re: self.re * other.re - self.im * other.im, 
            im: self.re * other.im + self.im * other.re 
        }
    }

    pub open spec fn scalar_mul(self, s: int) -> Complex {
        Complex { re: s * self.re, im: s * self.im }
    }
}

pub open spec fn cexp(theta: int) -> Complex {
    Complex { re: 1, im: 0 }
}

pub open spec fn complex_sum(n: nat, f: spec_fn(nat) -> Complex) -> Complex
    decreases n
{
    if n == 0 {
        Complex { re: 0, im: 0 }
    } else {
        f((n - 1) as nat).add(complex_sum((n - 1) as nat, f))
    }
}

fn ifft(a: Vec<Complex>) -> (result: Vec<Complex>)
    requires a.len() > 0,
    ensures
        result.len() == a.len(),
        forall|k: int| #[trigger] result[k] == result[k] && 0 <= k < result.len() ==> {
            let n = a.len() as nat;
            let expected = complex_sum(n, |j: nat| {
                if j < n {
                    a[j as int].mul(cexp(2 * k * (j as int)))
                } else {
                    Complex { re: 0, im: 0 }
                }
            }).scalar_mul(1);
            result[k] == expected
        }
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix struct literal syntax error by adding parentheses */
    let n = a.len();
    let mut result: Vec<Complex> = Vec::new();
    
    let mut k: usize = 0;
    while k < n
        invariant
            result.len() == k,
            0 <= k <= n,
            forall|i: int| 0 <= i < k ==> #[trigger] result[i] == {
                let expected = complex_sum(n as nat, |j: nat| {
                    if j < n as nat {
                        a[j as int].mul(cexp(2 * i * (j as int)))
                    } else {
                        Complex { re: 0, im: 0 }
                    }
                }).scalar_mul(1);
                expected
            },
    {
        ghost(let ghost_k = k as int);
        
        let mut sum_re: i64 = 0;
        let mut sum_im: i64 = 0;
        let mut j: usize = 0;
        
        while j < n
            invariant
                0 <= j <= n,
                (Complex { re: sum_re as int, im: sum_im as int }) == complex_sum(j as nat, |idx: nat| {
                    if idx < n as nat {
                        a[idx as int].mul(cexp(2 * ghost_k * (idx as int)))
                    } else {
                        Complex { re: 0, im: 0 }
                    }
                }),
        {
            let a_j = &a[j];
            let term_re = a_j.re as i64;
            let term_im = a_j.im as i64;
            sum_re = sum_re + term_re;
            sum_im = sum_im + term_im;
            j = j + 1;
        }
        
        result.push(Complex { re: sum_re as int, im: sum_im as int });
        k = k + 1;
    }
    
    result
}
// </vc-code>

}
fn main() {}