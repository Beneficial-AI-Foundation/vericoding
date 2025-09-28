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
fn sum_values(a: &Vec<i32>) -> (sum: i64)
    ensures
        sum == a@.map(|x: i32| x as int).fold_left(0,
            |acc: int, x: int| acc + x)
{
    /* helper modified by LLM (iteration 5): Confirmed i64 return for exec compatibility */
    let mut sum: i64 = 0;
    let mut i: usize = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            sum == a@.take(i as int).map(|x: i32| x as int).fold_left(0,
                |acc: int, x: int| acc + x)
        decreases a.len() - i
    {
        sum += a[i] as i64;
        i += 1;
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
    /* code modified by LLM (iteration 5): Removed as int cast to fix compilation error by avoiding int type usage in exec code */
    let total = sum_values(&a);
    let half_len = (a.len() / 2) + 1;
    let mut result = Vec::with_capacity(half_len);
    let c = Complex { re: total, im: 0 };
    let mut idx = 0;
    while idx < half_len
        invariant
            idx <= half_len,
            result.len() == idx,
            forall|k: int| 0 <= k < result.len() ==> result@[k] == c
        decreases half_len - idx
    {
        result.push(c);
        idx += 1;
    }
    result
}
// </vc-code>


}
fn main() {}