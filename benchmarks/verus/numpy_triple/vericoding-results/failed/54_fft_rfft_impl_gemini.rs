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
spec fn sum_int_seq(s: Seq<int>) -> int
    decreases s.len()
{
    if s.len() == 0 { 0 } else { s[0] + sum_int_seq(s.skip(1)) }
}

proof fn lemma_compute_dft_sum_is_real_sum(a: Seq<int>, k: nat, n: nat)
    requires n <= a.len()
    ensures
        compute_dft_sum(a, k, n).re == sum_int_seq(a.take(n as int)),
        compute_dft_sum(a, k, n).im == 0,
    decreases n
{
    if n > 0 {
        lemma_compute_dft_sum_is_real_sum(a, k, (n - 1) as nat);
    }
}

fn sum_vec(a: &Vec<i32>) -> (s: i32)
    requires a.len() > 0
    ensures s as int == sum_int_seq(vec_to_int_seq(a@))
{
    let mut sum: i32 = 0;
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            sum as int == sum_int_seq(vec_to_int_seq(a@.take(i as int))),
        decreases a.len() - i
    {
        sum = sum + a[i];
        i = i + 1;
    }
    sum
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
    let n = a.len();
    let result_len = (n / 2) + 1;

    let total_sum = sum_vec(&a);
    let a_int_seq = vec_to_int_seq(a@);

    let sum_complex = Complex { re: total_sum as int, im: 0 };

    assert forall|k: int| 0 <= k < result_len implies
        compute_dft_sum(a_int_seq, k as nat, n as nat) == sum_complex
    by {
        lemma_compute_dft_sum_is_real_sum(a_int_seq, k as nat, n as nat);
        assert(a_int_seq.take(n as int) == a_int_seq);
    };

    let mut result: Vec<Complex> = Vec::new();
    let mut k: usize = 0;
    while k < result_len
        invariant
            k <= result_len,
            result.len() == k,
            forall|j: int| 0 <= j < k ==> result[j] == sum_complex,
        decreases result_len - k
    {
        result.push(Complex { re: total_sum as int, im: 0 });
        k = k + 1;
    }
    
    result
}
// </vc-code>


}
fn main() {}