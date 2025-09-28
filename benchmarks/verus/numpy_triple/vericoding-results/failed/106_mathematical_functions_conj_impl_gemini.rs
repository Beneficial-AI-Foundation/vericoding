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
/* helper modified by LLM (iteration 3): re-confirmed helper correctness */
#[verifier::spinoff_prover]
proof fn lemma_conj_real(c: Complex)
    requires
        c.imag == 0,
    ensures
        c.conj() == c,
{
}

/* helper modified by LLM (iteration 3): re-confirmed helper correctness */
#[verifier::spinoff_prover]
proof fn lemma_conj_conj(c: Complex)
    ensures
        c.conj().conj() == c,
{
}

/* helper modified by LLM (iteration 5): added proof body */
#[verifier::spinoff_prover]
proof fn lemma_conj_norm_sq(c: Complex)
    ensures
        c.norm_sq() == c.conj().norm_sq(),
{
    assert(c.imag * c.imag == (-c.imag) * (-c.imag));
}

/* helper modified by LLM (iteration 3): re-confirmed helper correctness */
#[verifier::spinoff_prover]
proof fn lemma_conj_add(c1: Complex, c2: Complex)
    ensures
        c1.add(c2).conj() == c1.conj().add(c2.conj()),
{
}

/* helper modified by LLM (iteration 5): added proof body */
#[verifier::spinoff_prover]
proof fn lemma_conj_mul(c1: Complex, c2: Complex)
    ensures
        c1.mul(c2).conj() == c1.conj().mul(c2.conj()),
{
    let lhs = c1.mul(c2).conj();
    let rhs = c1.conj().mul(c2.conj());
    assert(lhs.real == rhs.real);
    assert(lhs.imag == rhs.imag);
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
    /* code modified by LLM (iteration 5): fixed implies/==> and completed proof blocks */
    let mut result: Vec<Complex> = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            i <= x.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == x@[j].conj(),
        decreases x.len() - i
    {
        let elem = &x[i];
        let conj_elem = Complex { real: elem.real, imag: -elem.imag };
        assert(conj_elem == elem.conj());
        result.push(conj_elem);
        i = i + 1;
    }

    assert forall|i: int| 0 <= i < x@.len() implies result@[i] == x@[i].conj() by {};
    
    assert forall|i: int| 0 <= i < x@.len() implies (x@[i].imag == 0 ==> result@[i] == x@[i]) by {
        if x@[i].imag == 0 {
            lemma_conj_real(x@[i]);
            assert(result@[i] == x@[i].conj());
            assert(x@[i].conj() == x@[i]);
        }
    };

    assert forall|i: int| 0 <= i < x@.len() implies result@[i].conj() == x@[i] by {
        assert(result@[i] == x@[i].conj());
        lemma_conj_conj(x@[i]);
        assert(x@[i].conj().conj() == x@[i]);
        assert(result@[i].conj() == x@[i].conj().conj());
    };

    assert forall|i: int| 0 <= i < x@.len() implies x@[i].norm_sq() == result@[i].norm_sq() by {
        assert(result@[i] == x@[i].conj());
        lemma_conj_norm_sq(x@[i]);
        assert(x@[i].norm_sq() == x@[i].conj().norm_sq());
        assert(result@[i].norm_sq() == x@[i].conj().norm_sq());
    };

    assert forall|i: int, y: Complex| 0 <= i < x@.len() implies x@[i].add(y).conj() == result@[i].add(y.conj()) by {
        assert(result@[i] == x@[i].conj());
        lemma_conj_add(x@[i], y);
        assert(x@[i].add(y).conj() == x@[i].conj().add(y.conj()));
        assert(result@[i].add(y.conj()) == x@[i].conj().add(y.conj()));
    };

    assert forall|i: int, y: Complex| 0 <= i < x@.len() implies x@[i].mul(y).conj() == result@[i].mul(y.conj()) by {
        assert(result@[i] == x@[i].conj());
        lemma_conj_mul(x@[i], y);
        assert(x@[i].mul(y).conj() == x@[i].conj().mul(y.conj()));
        assert(result@[i].mul(y.conj()) == x@[i].conj().mul(y.conj()));
    };

    result
}

// </vc-code>


}
fn main() {}