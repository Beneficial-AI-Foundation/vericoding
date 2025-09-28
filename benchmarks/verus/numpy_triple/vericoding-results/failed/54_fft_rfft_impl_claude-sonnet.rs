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
/* helper modified by LLM (iteration 5): Made helper spec function to avoid executable code type restrictions */
spec fn make_complex_from_sum(sum: int) -> Complex {
    Complex { re: sum, im: 0 }
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
    /* code modified by LLM (iteration 5): Use ghost variables and spec functions to avoid int type restrictions in executable code */
    let mut result = Vec::new();
    let n = a.len();
    let output_len = (n / 2) + 1;
    
    let mut k = 0;
    while k < output_len
        invariant
            0 <= k <= output_len,
            result.len() == k,
            output_len == (n / 2) + 1,
            n == a.len(),
            n > 0,
            forall|i: int| 0 <= i < k ==>
                result[i] == compute_dft_sum(vec_to_int_seq(a@), i as nat, n as nat)
    {
        let mut sum_re = 0i32;
        let mut j = 0;
        while j < n
            invariant
                0 <= j <= n,
                sum_re as int == (j as int) * (a[0] as int)
        {
            sum_re += a[j];
            j += 1;
        }
        
        let complex_result = Complex { re: sum_re as int, im: 0 };
        result.push(complex_result);
        k += 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}