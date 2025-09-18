// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): seq_complex_sum computes sum of first n elements of a sequence */
spec fn seq_complex_sum(a: Seq<Complex>, n: nat) -> Complex
    decreases n
{
    if n == 0 {
        Complex { re: 0, im: 0 }
    } else {
        a@(n - 1).add(seq_complex_sum(a, n - 1))
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
    /* code modified by LLM (iteration 5): compute total sum once and replicate for each output entry */
    let n = a.len();
    let n_int = n as int;

    let mut total = Complex { re: 0, im: 0 };
    let mut j: int = 0;
    while j < n_int
        invariant 0 <= j && j <= n_int,
        decreases n_int - j
    {
        let aj = a[j as usize];
        total = Complex { re: total.re + aj.re, im: total.im + aj.im };
        j = j + 1;
    }

    let mut result: Vec<Complex> = Vec::new();
    let mut k: int = 0;
    while k < n_int
        invariant 0 <= k && k <= n_int && result.len() == k as usize,
        decreases n_int - k
    {
        result.push(total);
        k = k + 1;
    }

    result
}
// </vc-code>

}
fn main() {}