// <vc-preamble>
use vstd::prelude::*;

verus! {

/* Complex number type for FFT results */
#[derive(PartialEq, Eq)]
pub struct Complex {
    pub re: int,
    pub im: int,
}

impl Complex {
    pub open spec fn zero() -> Complex {
        Complex { re: 0, im: 0 }
    }

    pub open spec fn add(self, other: Complex) -> Complex {
        Complex { re: self.re + other.re, im: self.im + other.im }
    }

    pub open spec fn mul(self, other: Complex) -> Complex {
        Complex { 
            re: self.re * other.re - self.im * other.im,
            im: self.re * other.im + self.im * other.re
        }
    }

    pub open spec fn from_real(x: int) -> Complex {
        Complex { re: x, im: 0 }
    }
}

pub open spec fn complex_sum(values: Seq<Complex>) -> Complex 
    decreases values.len()
{
    if values.len() == 0 {
        Complex::zero()
    } else {
        values[0].add(complex_sum(values.skip(1)))
    }
}

pub open spec fn dft_coefficient(a: Seq<int>, k: nat, j: nat) -> Complex {
    Complex::from_real(a[j as int])
}

pub open spec fn compute_dft_sum(a: Seq<int>, k: nat, n: nat) -> Complex 
    decreases n
{
    if n == 0 {
        Complex::zero()
    } else {
        dft_coefficient(a, k, (n - 1) as nat).add(compute_dft_sum(a, k, (n - 1) as nat))
    }
}

spec fn vec_to_int_seq(v: Seq<i32>) -> Seq<int> 
    decreases v.len()
{
    if v.len() == 0 {
        seq![]
    } else {
        seq![v[0] as int] + vec_to_int_seq(v.skip(1))
    }
}
// </vc-preamble>

// <vc-helpers>

    /* helper modified by LLM (iteration 5): ghost helpers for nat conversions */
    proof fn compute_dft_sum_ghost(a: Seq<int>, k: nat, n: nat) -> (sum: Complex)
        ensures sum == compute_dft_sum(a, k, n)
        decreases n
    {
        if n == 0 {
            Complex::zero()
        } else {
            dft_coefficient(a, k, (n - 1) as nat).add(compute_dft_sum_ghost(a, k, (n - 1) as nat))
        }
    }

    proof fn complex_sum_properties(values: Seq<Complex>)
        ensures complex_sum(values).re >= 0 || complex_sum(values).re <= 0,
        decreases values.len()
    {
        if values.len() > 0 {
            complex_sum_properties(values.skip(1));
        }
    }

    proof fn vec_to_int_seq_lemma(v: Seq<i32>)
        ensures vec_to_int_seq(v)@.len() == v@.len()
    {
        // Helper lemma about vec_to_int_seq length
    }

// </vc-helpers>

// <vc-spec>
fn rfft(a: Vec<i32>) -> (result: Vec<Complex>)
    requires a.len() > 0,
    ensures 
        result.len() == (a.len() / 2) + 1,
        forall|k: int| 0 <= k < result.len() ==> 
            result[k] == compute_dft_sum(vec_to_int_seq(a@), k as nat, a.len() as nat),
        result[0].im == 0,
        a.len() % 2 == 0 ==> result[(a.len() / 2) as int].im == 0
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): use ghost helper for DFT computation */
    let n = a.len();
    let mut result = Vec::new();
    let a_seq = vec_to_int_seq(a@);
    
    proof {
        vec_to_int_seq_lemma(a@);
    }
    
    let mut k: usize = 0;
    let max_k = (n / 2) + 1;
    while k < max_k
        invariant
            k <= max_k,
            result.len() == k,
            forall|i: int| 0 <= i < k ==> result[i] == compute_dft_sum(a_seq, i as nat, n as nat),
            k > 0 ==> result[0].im == 0,
            n % 2 == 0 ==> k > (n / 2) ==> result[(n / 2) as int].im == 0
        decreases max_k - k
    {
        let ghost sum = compute_dft_sum_ghost(a_seq, k as nat, n as nat);
        result.push(sum);
        k = k + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}