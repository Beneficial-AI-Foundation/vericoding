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
/* helper modified by LLM (iteration 4): prefix sum over ints */
pub open spec fn sum_prefix(a: Seq<int>, n: nat) -> int
    decreases n
{
    if n == 0 { 0 } else { sum_prefix(a, (n - 1) as nat) + a[(n - 1) as int] }
}

/* helper modified by LLM (iteration 4): spec wrapper avoiding nat casts in exec code */
pub open spec fn compute_dft_sum_usize(a: Seq<int>, k: usize, n: usize) -> Complex {
    compute_dft_sum(a, k as nat, n as nat)
}

/* helper modified by LLM (iteration 4): length preservation for vec_to_int_seq */
proof fn lemma_vec_to_int_seq_len(v: Seq<i32>)
    ensures vec_to_int_seq(v).len() == v.len()
    decreases v.len()
{
    if v.len() == 0 {
    } else {
        lemma_vec_to_int_seq_len(v.skip(1));
    }
}

/* helper modified by LLM (iteration 4): properties of Complex::from_real at zero */
proof fn lemma_from_real_zero()
    ensures Complex::zero() == Complex::from_real(0)
{
    assert(Complex::zero() == Complex::from_real(0));
}

/* helper modified by LLM (iteration 4): addition homomorphism for from_real */
proof fn lemma_from_real_add(x: int, y: int)
    ensures Complex::from_real(x).add(Complex::from_real(y)) == Complex::from_real(x + y)
{
    assert(Complex::from_real(x).add(Complex::from_real(y)).re == x + y);
    assert(Complex::from_real(x).add(Complex::from_real(y)).im == 0);
    assert(Complex::from_real(x + y).re == x + y);
    assert(Complex::from_real(x + y).im == 0);
    assert(Complex::from_real(x).add(Complex::from_real(y)) == Complex::from_real(x + y));
}

/* helper modified by LLM (iteration 4): compute_dft_sum equals from_real of prefix sum */
proof fn lemma_compute_dft_sum_eq_from_real_sum(a: Seq<int>, k: nat, n: nat)
    ensures compute_dft_sum(a, k, n) == Complex::from_real(sum_prefix(a, n))
    decreases n
{
    if n == 0 {
        lemma_from_real_zero();
        assert(compute_dft_sum(a, k, 0) == Complex::zero());
        assert(sum_prefix(a, 0) == 0);
        assert(Complex::zero() == Complex::from_real(0));
        assert(compute_dft_sum(a, k, 0) == Complex::from_real(sum_prefix(a, 0)));
    } else {
        lemma_compute_dft_sum_eq_from_real_sum(a, k, (n - 1) as nat);
        assert(compute_dft_sum(a, k, n) == dft_coefficient(a, k, (n - 1) as nat).add(compute_dft_sum(a, k, (n - 1) as nat)));
        assert(dft_coefficient(a, k, (n - 1) as nat) == Complex::from_real(a[(n - 1) as int]));
        let x = a[(n - 1) as int];
        let s = sum_prefix(a, (n - 1) as nat);
        assert(compute_dft_sum(a, k, (n - 1) as nat) == Complex::from_real(s));
        assert(compute_dft_sum(a, k, n) == Complex::from_real(x).add(Complex::from_real(s)));
        lemma_from_real_add(x, s);
        assert(Complex::from_real(x).add(Complex::from_real(s)) == Complex::from_real(x + s));
        assert(x + s == s + x);
        assert(s + x == sum_prefix(a, n));
        assert(compute_dft_sum(a, k, n) == Complex::from_real(sum_prefix(a, n)));
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
    /* code modified by LLM (iteration 4): construct vector of DFT sums using spec wrapper; prove postconditions */
    let n: usize = a.len();
    let L: usize = (n / 2) + 1;

    let mut r: Vec<Complex> = Vec::new();
    let mut j: usize = 0;
    while j < L
        invariant
            j <= L,
            r.len() == j,
            forall|kk: int|
                0 <= kk && kk < r.len() as int ==> r[kk] == compute_dft_sum(vec_to_int_seq(a@), kk as nat, n as nat),
        decreases L - j
    {
        let c = compute_dft_sum_usize(vec_to_int_seq(a@), j, n);
        proof {
            assert(c == compute_dft_sum(vec_to_int_seq(a@), j as nat, n as nat));
        }
        r.push(c);
        j = j + 1;
    }

    proof {
        assert(r.len() == L);

        assert forall |k: int|
            0 <= k && k < r.len() as int ==> r[k] == compute_dft_sum(vec_to_int_seq(a@), k as nat, n as nat)
        by {
            if 0 <= k && k < r.len() as int { }
        };

        // result[0].im == 0
        lemma_compute_dft_sum_eq_from_real_sum(vec_to_int_seq(a@), 0 as nat, n as nat);
        assert(r.len() > 0);
        assert(r[0] == compute_dft_sum(vec_to_int_seq(a@), 0 as nat, n as nat));
        assert(compute_dft_sum(vec_to_int_seq(a@), 0 as nat, n as nat) == Complex::from_real(sum_prefix(vec_to_int_seq(a@), n as nat)));
        assert(Complex::from_real(sum_prefix(vec_to_int_seq(a@), n as nat)).im == 0);

        // Nyquist imaginary part zero when length is even
        if n % 2 == 0 {
            let half: usize = n / 2;
            assert(half < r.len());
            lemma_compute_dft_sum_eq_from_real_sum(vec_to_int_seq(a@), half as nat, n as nat);
            assert(r[half as int] == compute_dft_sum(vec_to_int_seq(a@), half as nat, n as nat));
            assert(compute_dft_sum(vec_to_int_seq(a@), half as nat, n as nat) == Complex::from_real(sum_prefix(vec_to_int_seq(a@), n as nat)));
            assert(Complex::from_real(sum_prefix(vec_to_int_seq(a@), n as nat)).im == 0);
        }
    }

    r
}
// </vc-code>


}
fn main() {}