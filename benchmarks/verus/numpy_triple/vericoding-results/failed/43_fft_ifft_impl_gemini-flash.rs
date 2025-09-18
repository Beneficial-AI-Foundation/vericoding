// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed helper, as it causes compilation errors by returning an `int` for use in non-ghost code. The calculation will remain inlined in the code. */
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
/* code modified by LLM (iteration 5): corrected type casting errors by removing `as int` when assigning to `k` and `j` because `k_idx` and `j_idx` are usize, and `k` and `j` are later used in ghost code. */
{
    let n_usize = a.len();
    let n = n_usize as int;
    let mut result: Vec<Complex> = Vec::new();

    if n_usize == 0 {
        return result;
    }

    for k_idx in 0..n_usize {
        let k_scalar = k_idx as int;
        let mut current_sum = Complex { re: 0, im: 0 };

        for j_idx in 0..n_usize {
            let j_scalar = j_idx as int;
            let term = a[j_idx].mul(cexp(2 * k_scalar * j_scalar));
            current_sum = current_sum.add(term);
        }

        result.push(current_sum);
    }

    result
}
// </vc-code>

}
fn main() {}