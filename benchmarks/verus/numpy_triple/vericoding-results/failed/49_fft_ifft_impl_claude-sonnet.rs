// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn to_int(x: usize) -> int {
    x as int
}

proof fn lemma_complex_sum_step(n: nat, f: spec_fn(nat) -> Complex, j: nat)
    requires j < n,
    ensures complex_sum((j + 1) as nat, f) == f(j).add(complex_sum(j as nat, f))
{
    if j == 0 {
        assert(complex_sum(1, f) == f(0).add(complex_sum(0, f)));
    } else {
        lemma_complex_sum_step(n, f, (j - 1) as nat);
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
    /* code modified by LLM (iteration 5): Fixed int casting to use usize for executable code */
    let n = a.len();
    let mut result = Vec::with_capacity(n);
    let mut k = 0;
    while k < n
        invariant
            0 <= k <= n,
            result.len() == k,
            forall|i: int| 0 <= i < k ==> {
                let expected = complex_sum(n as nat, |j: nat| {
                    if j < n {
                        a[j as int].mul(cexp(2 * i * (j as int)))
                    } else {
                        Complex { re: 0int, im: 0int }
                    }
                }).scalar_mul(1int);
                result[i] == expected
            },
    {
        let mut sum = Complex { re: 0int, im: 0int };
        let mut j = 0;
        while j < n
            invariant
                0 <= j <= n,
                sum == complex_sum(j as nat, |idx: nat| {
                    if idx < n {
                        a[idx as int].mul(cexp(2 * (k as int) * (idx as int)))
                    } else {
                        Complex { re: 0int, im: 0int }
                    }
                }),
        {
            let ghost k_ghost = k as int;
            let ghost j_ghost = j as int;
            let term = a[j].mul(cexp(2 * k_ghost * j_ghost));
            sum = sum.add(term);
            j += 1;
        }
        let final_result = sum.scalar_mul(1int);
        result.push(final_result);
        k += 1;
    }
    result
}
// </vc-code>

}
fn main() {}