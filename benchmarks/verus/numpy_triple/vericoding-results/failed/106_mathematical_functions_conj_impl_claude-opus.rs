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
    /* code modified by LLM (iteration 5): Fixed syntax error in assert-by block */
    let mut result: Vec<Complex> = Vec::new();
    let mut i = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j].real == x@[j].real && result@[j].imag == -x@[j].imag,
            forall|j: int| 0 <= j < i ==> x@[j].imag == 0 ==> result@[j] == x@[j],
            forall|j: int| 0 <= j < i ==> result@[j].conj() == x@[j],
            forall|j: int| 0 <= j < i ==> x@[j].norm_sq() == result@[j].norm_sq(),
            forall|j: int, y: Complex| 0 <= j < i ==> x@[j].add(y).conj() == result@[j].add(y.conj()),
            forall|j: int, y: Complex| 0 <= j < i ==> x@[j].mul(y).conj() == result@[j].mul(y.conj()),
        decreases x.len() - i
    {
        let c = Complex { real: x[i].real, imag: -x[i].imag };
        
        proof {
            // Prove that c is the conjugate of x[i]
            assert(c.real == x[i].real);
            assert(c.imag == -x[i].imag);
            assert(c == x[i].conj());
            
            // Prove norm_sq is preserved
            assert(c.norm_sq() == c.real * c.real + c.imag * c.imag);
            assert(c.norm_sq() == x[i].real * x[i].real + (-x[i].imag) * (-x[i].imag));
            assert(c.norm_sq() == x[i].real * x[i].real + x[i].imag * x[i].imag);
            assert(c.norm_sq() == x[i].norm_sq());
            
            // Prove multiplication property
            assert forall|y: Complex| x[i].mul(y).conj() == c.mul(y.conj()) by {
                let prod_conj = x[i].mul(y).conj();
                let conj_prod = c.mul(y.conj());
                
                assert(prod_conj.real == x[i].real * y.real - x[i].imag * y.imag);
                assert(prod_conj.imag == -(x[i].real * y.imag + x[i].imag * y.real));
                
                assert(conj_prod.real == c.real * y.conj().real - c.imag * y.conj().imag);
                assert(conj_prod.real == x[i].real * y.real - (-x[i].imag) * (-y.imag));
                assert(conj_prod.real == x[i].real * y.real - x[i].imag * y.imag);
                
                assert(conj_prod.imag == c.real * y.conj().imag + c.imag * y.conj().real);
                assert(conj_prod.imag == x[i].real * (-y.imag) + (-x[i].imag) * y.real);
                assert(conj_prod.imag == -(x[i].real * y.imag + x[i].imag * y.real));
                
                assert(prod_conj == conj_prod);
            }
        }
        
        result.push(c);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}