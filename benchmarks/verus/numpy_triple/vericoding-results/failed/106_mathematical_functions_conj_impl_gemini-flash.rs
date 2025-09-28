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
/* helper modified by LLM (iteration 5): removed reference to `result` that is not in scope of function signature */
pub open spec fn vec_complex_conj(x: Seq<Complex>) -> Seq<Complex> {
    Seq::new(x.len(), |i: int| x[i].conj())
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
/* code modified by LLM (iteration 5): [no changes to the implementation logic, but updating the description for clarity] */
{
    let mut result = Vec::new();
    result.reserve(x.len());

    let mut i = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result.len() == i,
            // We need to prove that the `result` vector (the concrete implementation) matches the `vec_complex_conj` spec function at the end.
            // This includes showing that the length is correct and each element is the conjugate.
            forall|j: int| 0 <= j < i ==> result@[j] == x@[j].conj(),
             result@.len() == i,
            x@.len() == x.len()
        decreases x.len() - i
    {
        result.push(x[i].conj());
        i = i + 1;
    }

    proof {
        assert(result@ == vec_complex_conj(x@));
    }
    
    result
}
// </vc-code>


}
fn main() {}