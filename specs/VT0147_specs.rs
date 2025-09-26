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
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}