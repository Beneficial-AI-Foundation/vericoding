// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no changes, compilation errors are in vc-code */
pub exec fn complex_add(c1: Complex, c2: Complex) -> (result: Complex)
    ensures result == c1.add(c2),
{
    Complex { re: c1.re + c2.re, im: c1.im + c2.im }
}

proof fn lemma_complex_sum_extensionality(n: nat, f1: spec_fn(nat)->Complex, f2: spec_fn(nat)->Complex)
    requires forall|i: nat| i < n ==> f1(i) == f2(i),
    ensures complex_sum(n, f1) == complex_sum(n, f2),
    decreases n
{
    if n > 0 {
        lemma_complex_sum_extensionality((n-1) as nat, f1, f2);
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
    /* code modified by LLM (iteration 5): fixed compilation errors by adding 'as int' casts and removing redundant '.view()' calls in spec contexts */
    let n = a.len();
    let mut sum = Complex { re: 0 as int, im: 0 as int };
    let mut i: usize = 0;
    while i < n
        invariant
            0 <= i <= n,
            a.len() == n,
            sum == complex_sum(i as nat, |j: nat| a@[j as int]),
        decreases n - i
    {
        sum = complex_add(sum, a[i]);
        i = i + 1;
    }

    let mut result: Vec<Complex> = Vec::new();
    let mut k: usize = 0;
    while k < n
        invariant
            k <= n,
            result.len() == k,
            forall|j: int| 0 <= j < k ==> result@[j] == sum,
            sum == complex_sum(n as nat, |j: nat| a@[j as int]),
        decreases n - k
    {
        result.push(sum);
        k = k + 1;
    }

    proof {
        let n_nat = a.len() as nat;
        let simple_f = |j: nat| a@[j as int];
        assert(sum == complex_sum(n_nat, simple_f));

        assert forall|k: int| 0 <= k < (n as int) implies
            (complex_sum(n_nat, |j: nat| 
                if j < n_nat {
                    a@[j as int].mul(cexp(2 * k * (j as int)))
                } else {
                    Complex { re: 0, im: 0 }
                }
            ).scalar_mul(1)) == sum
        by {
            let expected_f = |j: nat| 
                if j < n_nat {
                    a@[j as int].mul(cexp(2 * k * (j as int)))
                } else {
                    Complex { re: 0, im: 0 }
                };

            assert forall|j: nat| j < n_nat implies expected_f(j) == simple_f(j) by {}
            lemma_complex_sum_extensionality(n_nat, expected_f, simple_f);
            
            let expected_sum = complex_sum(n_nat, expected_f);
            assert(expected_sum == sum);
            assert(expected_sum.scalar_mul(1) == expected_sum);
        };
    }

    result
}
// </vc-code>

}
fn main() {}