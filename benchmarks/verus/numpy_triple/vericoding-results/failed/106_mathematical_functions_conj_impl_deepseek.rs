// <vc-preamble>
use vstd::prelude::*;

verus! {

/* Structure representing a complex number with integer components */
#[derive(PartialEq, Eq)]
pub struct Complex {
    /* The real part of the complex number */
    pub real: int,
    /* The imaginary part of the complex number */
    pub imag: int,
}

impl Complex {
    /* Addition of complex numbers */
    pub open spec fn add(self, other: Complex) -> Complex {
        Complex { real: self.real + other.real, imag: self.imag + other.imag }
    }

    /* Multiplication of complex numbers */
    pub open spec fn mul(self, other: Complex) -> Complex {
        Complex { 
            real: self.real * other.real - self.imag * other.imag,
            imag: self.real * other.imag + self.imag * other.real
        }
    }

    /* Magnitude squared of a complex number */
    pub open spec fn norm_sq(self) -> int {
        self.real * self.real + self.imag * self.imag
    }

    /* Complex conjugate of a single complex number */
    pub open spec fn conj(self) -> Complex {
        Complex { real: self.real, imag: -self.imag }
    }
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_complex_conj_properties(x: Complex) 
    ensures
        x.conj().conj() == x,
        x.add(x.conj()).imag == 0,
        x.mul(x.conj()).imag == 0,
        x.mul(x.conj()).real == x.norm_sq()
decreases x
{
    assert(x.conj().real == x.real);
    assert(x.conj().imag == -x.imag);
    assert(x.conj().conj().real == x.real);
    assert(x.conj().conj().imag == x.imag);
    assert(x.add(x.conj()).imag == x.imag + x.conj().imag);
    let prod = x.mul(x.conj());
    assert(prod.real == x.real * x.conj().real - x.imag * x.conj().imag);
    assert(prod.imag == x.real * x.conj().imag + x.imag * x.conj().real);
    assert(x.norm_sq() == x.real * x.real + x.imag * x.imag);
}

proof fn lemma_complex_add_conj_property(x: Complex, y: Complex)
    ensures
        x.add(y).conj() == x.conj().add(y.conj())
decreases x
{
    let left = x.add(y).conj();
    let right = x.conj().add(y.conj());
    assert(left.real == x.real + y.real);
    assert(left.imag == -(x.imag + y.imag));
    assert(right.real == x.conj().real + y.conj().real);
    assert(right.imag == x.conj().imag + y.conj().imag);
    assert(x.conj().real == x.real);
    assert(y.conj().real == y.real);
    assert(x.conj().imag == -x.imag);
    assert(y.conj().imag == -y.imag);
}

proof fn lemma_complex_mul_conj_property(x: Complex, y: Complex)
    ensures
        x.mul(y).conj() == x.conj().mul(y.conj())
decreases x
{
    let left = x.mul(y).conj();
    let right = x.conj().mul(y.conj());
    
    assert(x.mul(y).real == x.real * y.real - x.imag * y.imag);
    assert(x.mul(y).imag == x.real * y.imag + x.imag * y.real);
    
    assert(left.real == x.real * y.real - x.imag * y.imag);
    assert(left.imag == -(x.real * y.imag + x.imag * y.real));
    
    assert(right.real == x.conj().real * y.conj().real - x.conj().imag * y.conj().imag);
    assert(right.imag == x.conj().real * y.conj().imag + x.conj().imag * y.conj().real);
    
    assert(x.conj().real == x.real);
    assert(x.conj().imag == -x.imag);
    assert(y.conj().real == y.real);
    assert(y.conj().imag == -y.imag);
    
    assert(right.real == x.real * y.real - (-x.imag) * (-y.imag));
    assert(right.real == x.real * y.real - x.imag * y.imag);
    
    assert(right.imag == x.real * (-y.imag) + (-x.imag) * y.real);
    assert(right.imag == -x.real * y.imag - x.imag * y.real);
    assert(right.imag == -(x.real * y.imag + x.imag * y.real));
}
// </vc-helpers>

// <vc-spec>
fn conj(x: Vec<Complex>) -> (result: Vec<Complex>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < x@.len() ==> 
            result@[i].real == x@[i].real && result@[i].imag == -x@[i].imag,
        forall|i: int| 0 <= i < x@.len() ==> 
            x@[i].imag == 0 ==> result@[i] == x@[i],
        forall|i: int| 0 <= i < x@.len() ==> 
            result@[i].conj() == x@[i],
        forall|i: int| 0 <= i < x@.len() ==> 
            x@[i].norm_sq() == result@[i].norm_sq(),
        forall|i: int, y: Complex| 0 <= i < x@.len() ==> 
            x@[i].add(y).conj() == result@[i].add(y.conj()),
        forall|i: int, y: Complex| 0 <= i < x@.len() ==> 
            x@[i].mul(y).conj() == result@[i].mul(y.conj())
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed compilation error by removing proof blocks from spec functions */
    let mut result: Vec<Complex> = Vec::new();
    let mut i: usize = 0;
    
    while i < x.len()
        invariant
            0 <= i <= x@.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j].real == x@[j].real && result@[j].imag == -x@[j].imag,
            forall|j: int| 0 <= j < i ==> result@[j].conj() == x@[j],
            forall|j: int| 0 <= j < i ==> x@[j].norm_sq() == result@[j].norm_sq(),
            forall|j: int| 0 <= j < i ==> x@[j].imag == 0 ==> result@[j] == x@[j],
            forall|j: int, y: Complex| 0 <= j < i ==> x@[j].add(y).conj() == result@[j].add(y.conj()),
            forall|j: int, y: Complex| 0 <= j < i ==> x@[j].mul(y).conj() == result@[j].mul(y.conj())
        decreases x@.len() - i
    {
        let orig = x[i];
        let conj_elem = Complex { real: orig.real, imag: -orig.imag };
        result.push(conj_elem);
        
        proof {
            lemma_complex_conj_properties(orig);
        }
        
        i += 1;
    }
    result
}
// </vc-code>


}
fn main() {}