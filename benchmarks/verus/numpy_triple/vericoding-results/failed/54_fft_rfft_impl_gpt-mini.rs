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
/* helper modified by LLM (iteration 5): int_seq_sum_prefix: sum prefix of int sequence */
pub open spec fn int_seq_sum_prefix(a: Seq<int>, n: nat) -> int
    decreases n
{
    if n == 0 {
        0
    } else {
        a[(n - 1) as int] + int_seq_sum_prefix(a, n - 1)
    }
}

/* helper modified by LLM (iteration 5): compute_dft_sum_eq_from_real_sum: relate compute_dft_sum to real sum */
pub proof fn compute_dft_sum_eq_from_real_sum(a: Seq<int>, k: nat, n: nat)
    ensures compute_dft_sum(a, k, n) == Complex::from_real(int_seq_sum_prefix(a, n)),
    decreases n
{
    if n == 0 {
    } else {
        compute_dft_sum_eq_from_real_sum(a, k, n - 1);
        proof {
            assert(compute_dft_sum(a, k, n) == dft_coefficient(a, k, (n - 1) as nat).add(compute_dft_sum(a, k, n - 1)));
            assert(dft_coefficient(a, k, (n - 1) as nat) == Complex::from_real(a[(n - 1) as int]));
            assert(compute_dft_sum(a, k, n - 1) == Complex::from_real(int_seq_sum_prefix(a, n - 1)));
            assert(Complex::from_real(a[(n - 1) as int]).add(Complex::from_real(int_seq_sum_prefix(a, n - 1))) == Complex::from_real(a[(n - 1) as int] + int_seq_sum_prefix(a, n - 1)));
            assert(Complex::from_real(a[(n - 1) as int] + int_seq_sum_prefix(a, n - 1)) == Complex::from_real(int_seq_sum_prefix(a, n)));
            assert(compute_dft_sum(a, k, n) == Complex::from_real(int_seq_sum_prefix(a, n)));
        }
    }
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
    /* code modified by LLM (iteration 5): construct result filled with the real sum (spec) using helpers */
    let n_usize: usize = a.len();
    let m_usize: usize = (n_usize / 2) + 1;

    let mut result: Vec<Complex> = Vec::new();

    let total_spec: int = int_seq_sum_prefix(vec_to_int_seq(a@), a.len() as nat);

    let mut i: usize = 0;
    while i < m_usize
        invariant
            i <= m_usize,
            result.len() == i,
        decreases m_usize - i
    {
        result.push(Complex { re: total_spec, im: 0 });
        i = i + 1;
    }

    proof {
        compute_dft_sum_eq_from_real_sum(vec_to_int_seq(a@), 0, a.len() as nat);

        let mut j: usize = 0;
        while j < m_usize
            invariant
                j <= m_usize,
            decreases m_usize - j
        {
            assert(result[j] == Complex::from_real(total_spec));
            j = j + 1;
        }

        assert(result.len() == m_usize);
        assert(result[0].im == 0);
        if a.len() % 2 == 0 {
            assert(result[(a.len() / 2) as int].im == 0);
        }
    }

    result
}

// </vc-code>


}
fn main() {}