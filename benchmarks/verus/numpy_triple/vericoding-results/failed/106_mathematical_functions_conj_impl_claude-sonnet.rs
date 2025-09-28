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
/* helper modified by LLM (iteration 5): fixed multiplication lemma assertions with correct arithmetic */
/* Lemma proving properties of complex conjugation for addition */
proof fn lemma_conj_add(x: Complex, y: Complex)
    ensures
        x.add(y).conj() == x.conj().add(y.conj())
{
}

/* Lemma proving properties of complex conjugation for multiplication */
proof fn lemma_conj_mul(x: Complex, y: Complex)
    ensures
        x.mul(y).conj() == x.conj().mul(y.conj())
{
    let xy = x.mul(y);
    let xc = x.conj();
    let yc = y.conj();
    
    assert(xy.real == x.real * y.real - x.imag * y.imag);
    assert(xy.imag == x.real * y.imag + x.imag * y.real);
    
    let left = xy.conj();
    assert(left.real == xy.real);
    assert(left.imag == -xy.imag);
    
    let right = xc.mul(yc);
    assert(right.real == x.real * y.real - (-x.imag) * (-y.imag));
    assert(right.imag == x.real * (-y.imag) + (-x.imag) * y.real);
    
    assert((-x.imag) * (-y.imag) == x.imag * y.imag);
    assert(right.real == x.real * y.real - x.imag * y.imag);
    assert(right.imag == -x.real * y.imag - x.imag * y.real);
    assert(right.imag == -(x.real * y.imag + x.imag * y.real));
    
    assert(left.real == right.real);
    assert(left.imag == right.imag);
}

/* Lemma proving that conjugation preserves magnitude squared */
proof fn lemma_conj_norm_sq(x: Complex)
    ensures
        x.norm_sq() == x.conj().norm_sq()
{
    let xc = x.conj();
    assert(xc.real == x.real && xc.imag == -x.imag);
    assert(xc.norm_sq() == xc.real * xc.real + xc.imag * xc.imag);
    assert((-x.imag) * (-x.imag) == x.imag * x.imag);
    assert(xc.norm_sq() == x.real * x.real + x.imag * x.imag);
}

/* Lemma proving that double conjugation returns original complex number */
proof fn lemma_double_conj(x: Complex)
    ensures
        x.conj().conj() == x
{
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
    /* code modified by LLM (iteration 5): added decreases clause to fix compilation error */
    let mut result: Vec<Complex> = Vec::new();
    let mut i = 0;
    
    while i < x.len()
        invariant
            result.len() == i,
            i <= x.len(),
            forall|j: int| 0 <= j < i ==> 
                result@[j].real == x@[j].real && result@[j].imag == -x@[j].imag,
            forall|j: int| 0 <= j < i ==> 
                result@[j].conj() == x@[j],
            forall|j: int| 0 <= j < i ==> 
                x@[j].norm_sq() == result@[j].norm_sq()
        decreases x.len() - i
    {
        let conj_elem = Complex {
            real: x[i].real,
            imag: -x[i].imag
        };
        
        proof {
            lemma_double_conj(x@[i as int]);
            lemma_conj_norm_sq(x@[i as int]);
        }
        
        result.push(conj_elem);
        i += 1;
    }
    
    proof {
        assert forall|j: int, y: Complex| 0 <= j < x@.len() implies
            x@[j].add(y).conj() == result@[j].add(y.conj()) by {
            lemma_conj_add(x@[j], y);
        };
        
        assert forall|j: int, y: Complex| 0 <= j < x@.len() implies
            x@[j].mul(y).conj() == result@[j].mul(y.conj()) by {
            lemma_conj_mul(x@[j], y);
        };
    }
    
    result
}
// </vc-code>


}
fn main() {}