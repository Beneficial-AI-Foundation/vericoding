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
/* helper modified by LLM (iteration 5): Fixed compute_dft_sum_exec to return Complex properly */
proof fn lemma_vec_to_int_seq_len(v: Seq<i32>)
    ensures vec_to_int_seq(v).len() == v.len()
    decreases v.len()
{
    if v.len() == 0 {
    } else {
        lemma_vec_to_int_seq_len(v.skip(1));
    }
}

proof fn lemma_vec_to_int_seq_index(v: Seq<i32>, i: int)
    requires
        0 <= i < v.len()
    ensures
        vec_to_int_seq(v)[i] == v[i] as int
    decreases v.len()
{
    if i == 0 {
    } else {
        lemma_vec_to_int_seq_index(v.skip(1), i - 1);
    }
}

fn compute_dft_sum_exec(a: &Vec<i32>, k: usize) -> (result: Complex)
    requires
        a.len() > 0,
        k < a.len()
    ensures
        result == compute_dft_sum(vec_to_int_seq(a@), k as nat, a.len() as nat)
{
    let mut sum_re: i32 = 0;
    let mut sum_im: i32 = 0;
    let mut j: usize = 0;
    let mut partial_sum: Complex = Complex { re: 0, im: 0 };
    
    while j < a.len()
        invariant
            j <= a.len(),
            partial_sum == compute_dft_sum_partial(vec_to_int_seq(a@), k as nat, j as nat),
            partial_sum.re == sum_re as int,
            partial_sum.im == sum_im as int
    {
        let coeff_re = a[j];
        sum_re = sum_re + coeff_re;
        partial_sum = Complex { re: sum_re as int, im: sum_im as int };
        j = j + 1;
    }
    
    proof {
        lemma_compute_dft_sum_partial_complete(vec_to_int_seq(a@), k as nat, a.len() as nat);
        assert(partial_sum == compute_dft_sum(vec_to_int_seq(a@), k as nat, a.len() as nat));
    }
    
    partial_sum
}

spec fn compute_dft_sum_partial(a: Seq<int>, k: nat, j: nat) -> Complex
    decreases j
{
    if j == 0 {
        Complex::zero()
    } else {
        dft_coefficient(a, k, (j - 1) as nat).add(compute_dft_sum_partial(a, k, (j - 1) as nat))
    }
}

proof fn lemma_compute_dft_sum_partial_complete(a: Seq<int>, k: nat, n: nat)
    ensures
        compute_dft_sum_partial(a, k, n) == compute_dft_sum(a, k, n)
    decreases n
{
    if n == 0 {
    } else {
        lemma_compute_dft_sum_partial_complete(a, k, (n - 1) as nat);
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
    /* code modified by LLM (iteration 5): Call compute_dft_sum_exec to get actual Complex values */
    let n = a.len();
    let output_size = (n / 2) + 1;
    let mut result: Vec<Complex> = Vec::new();
    let mut k: usize = 0;
    
    while k < output_size
        invariant
            k <= output_size,
            output_size == (n / 2) + 1,
            n == a.len(),
            n > 0,
            result.len() == k,
            forall|i: int| 0 <= i < k ==> result[i] == compute_dft_sum(vec_to_int_seq(a@), i as nat, n as nat)
    {
        let coeff = compute_dft_sum_exec(&a, k);
        result.push(coeff);
        k = k + 1;
    }
    
    proof {
        assert(result.len() == output_size);
        assert(forall|k: int| 0 <= k < result.len() ==> 
            result[k] == compute_dft_sum(vec_to_int_seq(a@), k as nat, a.len() as nat));
        assert(result[0] == compute_dft_sum(vec_to_int_seq(a@), 0 as nat, a.len() as nat));
        assert(result[0].im == 0);
        if a.len() % 2 == 0 {
            assert(result[(a.len() / 2) as int] == compute_dft_sum(vec_to_int_seq(a@), (a.len() / 2) as nat, a.len() as nat));
            assert(result[(a.len() / 2) as int].im == 0);
        }
    }
    
    result
}
// </vc-code>


}
fn main() {}