// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): changed compute_complex_vector_sum to a proof function to handle ghost types */
proof fn lemma_add_commutative(c1: Complex, c2: Complex)
    ensures c1.add(c2) == c2.add(c1)
{
}

proof fn lemma_mul_id(c: Complex)
    ensures c.mul(Complex{re: 1, im: 0}) == c
{
}

proof fn lemma_scalar_mul_1(c: Complex)
    ensures c.scalar_mul(1) == c
{
}

proof fn lemma_equal_functions_imply_equal_sums(n: nat, f1: spec_fn(nat) -> Complex, f2: spec_fn(nat) -> Complex)
    requires forall|j: nat| #[trigger] f1(j) == f2(j),
    ensures complex_sum(n, f1) == complex_sum(n, f2),
    decreases n
{
    if n > 0 {
        lemma_equal_functions_imply_equal_sums((n - 1) as nat, f1, f2);
    }
}

proof fn compute_complex_vector_sum(a: &Vec<Complex>) -> (sum: Complex)
    requires a.len() > 0,
    ensures sum == complex_sum(a.len() as nat, |j: nat| if j < a.len() as nat { a@[(j as int)] } else { Complex{re: 0, im: 0} }),
{
    let n = a.len() as nat;
    let f = |j: nat| if j < n { a@[(j as int)] } else { Complex{re: 0, im: 0} };

    let mut sum = Complex { re: 0, im: 0 };
    let mut i: nat = 0;

    while i < n
        invariant
            0 <= i <= n,
            a.len() == n as usize,
            sum == complex_sum(i, f),
        decreases n - i
    {
        lemma_add_commutative(sum, a@[i as int]);
        sum = sum.add(a@[i as int]);
        i = i + 1;
    }
    sum
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
    /* code modified by LLM (iteration 3): treat as proof function body, use Vec::new, fix proof logic */
    let n = a.len();
    let n_nat = n as nat;

    let total_sum = compute_complex_vector_sum(a);

    let mut result: Vec<Complex> = Vec::new();
    let mut k: nat = 0;
    while k < n_nat
        invariant
            0 <= k <= n_nat,
            result.len() == k as usize,
            a.len() == n,
            total_sum == complex_sum(n_nat, |j: nat| if j < n_nat { a@[(j as int)] } else { Complex {re:0, im:0} }),
            forall|i: int| 0 <= i < k ==> result@[i] == total_sum,
        decreases n_nat - k
    {
        result.push(total_sum);
        k = k + 1;
    }

    assert forall|k_int: int| 0 <= k_int < result.len() implies #[trigger] result@[k_int] == result@[k_int] && {
        let expected = complex_sum(n_nat, |j: nat| {
            if j < n_nat {
                a[j as int].mul(cexp(2 * k_int * (j as int)))
            } else {
                Complex { re: 0, im: 0 }
            }
        }).scalar_mul(1);
        result@[k_int] == expected
    } by {
        let f1 = |j: nat| if j < n_nat { a@[(j as int)] } else { Complex {re:0, im:0} };
        let f2 = |j: nat| if j < n_nat { a[j as int].mul(cexp(2 * k_int * (j as int))) } else { Complex { re: 0, im: 0 } };

        assert forall |j: nat| f1(j) == f2(j) by {
            if j < n_nat {
                lemma_mul_id(a@[j as int]);
            }
        }
        lemma_equal_functions_imply_equal_sums(n_nat, f1, f2);
        
        let sum_f2 = complex_sum(n_nat, f2);
        assert(total_sum == sum_f2);
        
        lemma_scalar_mul_1(sum_f2);
        let expected = sum_f2.scalar_mul(1);
        assert(expected == sum_f2);

        assert(result@[k_int] == total_sum);
        assert(result@[k_int] == expected);
    };

    result
}
// </vc-code>

}
fn main() {}