// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): fixed compute_ifft_value implementation to actually compute the IFFT value instead of returning zero */
spec fn zero_complex() -> Complex {
    Complex { re: 0, im: 0 }
}

spec fn conjugate(c: Complex) -> Complex {
    Complex { re: c.re, im: -c.im }
}

fn compute_ifft_value(a: &Vec<Complex>, k: usize) -> (result: Complex)
    requires a.len() > 0, k < a.len()
    ensures {
        let n = a.len() as nat;
        let expected = complex_sum(n, |j: nat| {
            if j < n {
                a[j as int].mul(cexp(2 * (k as int) * (j as int)))
            } else {
                Complex { re: 0, im: 0 }
            }
        }).scalar_mul(1);
        result == expected
    }
{
    let n = a.len();
    let mut sum = Complex { re: 0, im: 0 };
    
    for j in 0..n
        invariant
            sum == complex_sum(j as nat, |idx: nat| {
                if idx < n {
                    a[idx as int].mul(cexp(2 * (k as int) * (idx as int)))
                } else {
                    Complex { re: 0, im: 0 }
                }
            })
    {
        let term = a[j].mul(cexp(2 * (k as int) * (j as int)));
        sum = sum.add(term);
    }
    
    sum
}

proof fn complex_sum_extensionality(n: nat, f: spec_fn(nat) -> Complex, g: spec_fn(nat) -> Complex)
    requires forall|i: nat| i < n ==> f(i) == g(i)
    ensures complex_sum(n, f) == complex_sum(n, g)
    decreases n
{
    if n > 0 {
        complex_sum_extensionality((n - 1) as nat, f, g);
    }
}
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
    /* code modified by LLM (iteration 5): fixed ensures clause by removing extra braces and correcting syntax */
    let n = a.len();
    let mut result = Vec::with_capacity(n);
    
    for k in 0..n
        invariant
            result.len() == k,
            n == a.len(),
            forall|i: int| 0 <= i < k ==> {
                let expected = complex_sum(n as nat, |j: nat| {
                    if j < n {
                        a[j as int].mul(cexp(2 * i * (j as int)))
                    } else {
                        Complex { re: 0, im: 0 }
                    }
                }).scalar_mul(1);
                result[i] == expected
            }
    {
        let sum_val = compute_ifft_value(&a, k);
        result.push(sum_val);
    }
    
    result
}
// </vc-code>

}
fn main() {}