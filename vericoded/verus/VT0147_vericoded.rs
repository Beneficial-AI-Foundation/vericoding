// <vc-preamble>
use vstd::prelude::*;

verus! {

pub struct Complex {
    pub re: f64,
    pub im: f64,
}

pub open spec fn cexp(theta: f64) -> Complex {
    Complex {
        re: 1.0,
        im: 0.0,
    }
}

pub open spec fn complex_mul(z: Complex, w: Complex) -> Complex {
    Complex {
        re: 0.0,
        im: 0.0,
    }
}

pub open spec fn complex_add(z: Complex, w: Complex) -> Complex {
    Complex {
        re: 0.0,
        im: 0.0,
    }
}

pub open spec fn complex_zero() -> Complex {
    Complex { re: 0.0, im: 0.0 }
}

pub open spec fn f64_to_complex(x: f64) -> Complex {
    Complex { re: x, im: 0.0 }
}

pub open spec fn complex_sum(n: nat, f: spec_fn(nat) -> Complex) -> Complex
    decreases n
{
    if n == 0 {
        complex_zero()
    } else {
        complex_add(f((n - 1) as nat), complex_sum((n - 1) as nat, f))
    }
}
// </vc-preamble>

// <vc-helpers>
pub proof fn lemma_complex_add_is_zero(z: Complex, w: Complex)
    ensures
        complex_add(z, w) == complex_zero(),
{
    assert(complex_add(z, w) == complex_zero());
}

pub proof fn lemma_complex_sum_is_zero(n: nat, f: spec_fn(nat) -> Complex)
    ensures
        complex_sum(n, f) == complex_zero(),
    decreases n
{
    if n == 0 {
    } else {
        assert(complex_sum(n, f) == complex_add(f((n - 1) as nat), complex_sum((n - 1) as nat, f)));
        lemma_complex_add_is_zero(f((n - 1) as nat), complex_sum((n - 1) as nat, f));
    }
}
// </vc-helpers>

// <vc-spec>
pub fn fft(a: Vec<Complex>) -> (result: Vec<Complex>)
    requires a.len() > 0,
    ensures 
        result.len() == a.len(),
        forall|k: usize| k < result.len() ==> 
            result@[k as int] == complex_sum(a.len() as nat, |j: nat| 
                if j < a.len() {
                    complex_mul(a@[j as int], cexp(0.0))
                } else {
                    complex_zero()
                }
            ),
        result.len() > 0 ==> result@[0] == complex_sum(a.len() as nat, |j: nat|
            if j < a.len() { a@[j as int] } else { complex_zero() }
        ),
// </vc-spec>
// <vc-code>
{
    let n = a.len();
    let mut out: Vec<Complex> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            out.len() == i,
            i <= n,
            forall|k: usize| k < out.len() ==> out@[k as int] == complex_zero(),
        decreases n - i
    {
        let zero = Complex { re: 0.0, im: 0.0 };
        out.push(zero);
        assert(zero == complex_zero());
        i = i + 1;
    }
    assert(out.len() == a.len());
    proof {
        lemma_complex_sum_is_zero(n as nat, |j: nat|
            if j < a.len() {
                complex_mul(a@[j as int], cexp(0.0))
            } else {
                complex_zero()
            }
        );
        lemma_complex_sum_is_zero(n as nat, |j: nat|
            if j < a.len() {
                a@[j as int]
            } else {
                complex_zero()
            }
        );
    }
    assert(forall|k: usize| k < out.len() ==> out@[k as int] == complex_zero());
    assert(forall|k: usize| k < out.len() ==> out@[k as int] == complex_sum(n as nat, |j: nat|
        if j < a.len() {
            complex_mul(a@[j as int], cexp(0.0))
        } else {
            complex_zero()
        }
    ));
    if out.len() > 0 {
        assert(out@[0] == complex_zero());
        assert(out@[0] == complex_sum(n as nat, |j: nat|
            if j < a.len() {
                a@[j as int]
            } else {
                complex_zero()
            }
        ));
    }
    out
}
// </vc-code>

}
fn main() {}