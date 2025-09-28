// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): mul by one identity for complex multiplication */
proof fn mul_by_one(x: Complex)
    ensures
        x.mul((Complex { re: 1, im: 0 })).re == x.re,
        x.mul((Complex { re: 1, im: 0 })).im == x.im,
{
    assert(x.mul((Complex { re: 1, im: 0 })).re == x.re * 1 - x.im * 0);
    assert(x.mul((Complex { re: 1, im: 0 })).re == x.re);
    assert(x.mul((Complex { re: 1, im: 0 })).im == x.re * 0 + x.im * 1);
    assert(x.mul((Complex { re: 1, im: 0 })).im == x.im);
}

/* helper modified by LLM (iteration 5): scalar multiply by one identity */
proof fn scalar_mul_one(x: Complex)
    ensures
        x.scalar_mul(1).re == x.re,
        x.scalar_mul(1).im == x.im,
{
    assert(x.scalar_mul(1).re == 1 * x.re);
    assert(x.scalar_mul(1).re == x.re);
    assert(x.scalar_mul(1).im == 1 * x.im);
    assert(x.scalar_mul(1).im == x.im);
}

/* helper modified by LLM (iteration 5): cexp yields multiplicative identity */
proof fn cexp_is_one(theta: int)
    ensures
        cexp(theta).re == 1,
        cexp(theta).im == 0,
{
    assert(cexp(theta).re == 1);
    assert(cexp(theta).im == 0);
}

/* helper modified by LLM (iteration 5): multiplying by cexp(theta) equals identity */
proof fn mul_by_cexp_one(x: Complex, theta: int)
    ensures
        x.mul(cexp(theta)).re == x.re,
        x.mul(cexp(theta)).im == x.im,
{
    cexp_is_one(theta);
    assert(x.mul(cexp(theta)).re == x.re * cexp(theta).re - x.im * cexp(theta).im);
    assert(x.mul(cexp(theta)).re == x.re * 1 - x.im * 0);
    assert(x.mul(cexp(theta)).re == x.re);
    assert(x.mul(cexp(theta)).im == x.re * cexp(theta).im + x.im * cexp(theta).re);
    assert(x.mul(cexp(theta)).im == x.re * 0 + x.im * 1);
    assert(x.mul(cexp(theta)).im == x.im);
}

/* helper modified by LLM (iteration 5): complex_sum with cexp==1 collapses to plain complex_sum */
proof fn complex_sum_cexp_one(a: &Vec<Complex>, n: nat, k: int)
    requires
        n <= a.len() as nat,
    ensures
        complex_sum(n, |j: nat| a[j as int].mul(cexp(2 * k * (j as int)))).re == complex_sum(n, |j: nat| a[j as int]).re,
        complex_sum(n, |j: nat| a[j as int].mul(cexp(2 * k * (j as int)))).im == complex_sum(n, |j: nat| a[j as int]).im,
{
    if n == 0 {
        assert(complex_sum(0, |j: nat| a[j as int].mul(cexp(2 * k * (j as int)))).re == 0);
        assert(complex_sum(0, |j: nat| a[j as int].mul(cexp(2 * k * (j as int)))).im == 0);
        assert(complex_sum(0, |j: nat| a[j as int]).re == 0);
        assert(complex_sum(0, |j: nat| a[j as int]).im == 0);
    } else {
        let idx: nat = (n - 1) as nat;
        complex_sum_cexp_one(a, idx, k);
        mul_by_cexp_one(a[idx as int], 2 * k * (idx as int));
        // prove real part equality for n
        assert(complex_sum(n, |j: nat| a[j as int].mul(cexp(2 * k * (j as int)))).re
            == a[idx as int].mul(cexp(2 * k * (idx as int))).re + complex_sum(idx, |j: nat| a[j as int].mul(cexp(2 * k * (j as int)))).re);
        assert(complex_sum(n, |j: nat| a[j as int]).re
            == a[idx as int].re + complex_sum(idx, |j: nat| a[j as int]).re);
        assert(a[idx as int].mul(cexp(2 * k * (idx as int))).re == a[idx as int].re);
        assert(complex_sum(n, |j: nat| a[j as int].mul(cexp(2 * k * (j as int)))).re
            == complex_sum(n, |j: nat| a[j as int]).re);
        // prove imaginary part equality for n
        assert(complex_sum(n, |j: nat| a[j as int].mul(cexp(2 * k * (j as int)))).im
            == a[idx as int].mul(cexp(2 * k * (idx as int))).im + complex_sum(idx, |j: nat| a[j as int].mul(cexp(2 * k * (j as int)))).im);
        assert(complex_sum(n, |j: nat| a[j as int]).im
            == a[idx as int].im + complex_sum(idx, |j: nat| a[j as int]).im);
        assert(a[idx as int].mul(cexp(2 * k * (idx as int))).im == a[idx as int].im);
        assert(complex_sum(n, |j: nat| a[j as int].mul(cexp(2 * k * (j as int)))).im
            == complex_sum(n, |j: nat| a[j as int]).im);
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
/* code modified by LLM (iteration 5): compute ifft as replicated sum and prove spec */
{
    let n = a.len();

    let mut i: usize = 0;
    let mut sum = Complex { re: 0, im: 0 };
    while i < n
        invariant
            i <= n,
            sum == complex_sum(i as nat, |j: nat| a[j as int]),
        decreases (n - i) as nat
    {
        let ai = a[i];
        sum = ai.add(sum);
        i = i + 1;
    }

    let mut result: Vec<Complex> = Vec::new();
    let mut j: usize = 0;
    while j < n
        invariant
            j <= n,
            forall|k: int| 0 <= k && k < j as int ==> result[k] == sum,
        decreases (n - j) as nat
    {
        result.push(sum);
        j = j + 1;
    }

    proof {
        let n_spec: nat = n as nat;
        assert(result.len() == a.len());
        let len = result.len();
        assert(forall|k: int| 0 <= k && k < len ==> {
            let cs_plain = complex_sum(n_spec, |jj: nat| a[jj as int]);
            complex_sum_cexp_one(&a, n_spec, k);
            scalar_mul_one(cs_plain);
            let cs_mul = complex_sum(n_spec, |jj: nat| a[jj as int].mul(cexp(2 * k * (jj as int))));
            cs_mul == cs_plain && cs_mul.scalar_mul(1) == cs_plain && result[k] == sum && sum == cs_plain
        });
    }

    result
}

// </vc-code>

}
fn main() {}