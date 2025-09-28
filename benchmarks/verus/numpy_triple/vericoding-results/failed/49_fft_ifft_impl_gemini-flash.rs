// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

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
/* code modified by LLM (iteration 5): Cast k and j to int type only for the cexp function call, not for array access */
{
    let n_usize = a.len();
    let n = a.len();
    let mut result: Vec<Complex> = Vec::new();
    result.reserve(n_usize);

    let mut k: usize = 0;
    while k < n_usize
        invariant
            result.len() == k,
            k <= n_usize,
            forall|idx: int| 0 <= idx && (idx as usize) < k ==> {
                let expected = complex_sum(n as nat, |j_idx: nat| {
                    if j_idx < n as nat {
                        a[j_idx as usize].mul(cexp(2 * idx * (j_idx as int)))
                    } else {
                        Complex { re: 0, im: 0 }
                    }
                }).scalar_mul(1);
                result[idx as usize] == expected
            },
        decreases n_usize - k
    {
        let mut current_sum = Complex { re: 0, im: 0 };
        let mut j: usize = 0;
        while j < n_usize
            invariant
                j <= n_usize,
                current_sum == complex_sum(j as nat, |idx_j: nat| {
                    if idx_j < n as nat {
                        a[idx_j as usize].mul(cexp(2 * k as int * (idx_j as int)))
                    } else {
                        Complex { re: 0, im: 0 }
                    }
                }),
            decreases n_usize - j
        {
            let term = a[j].mul(cexp(2 * k as int * j as int));
            current_sum = current_sum.add(term);
            j = j + 1;
        }

        result.push(current_sum.scalar_mul(1));
        k = k + 1;
    }

    result
}
// </vc-code>

}
fn main() {}