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
/* helper modified by LLM (iteration 5): conj involution */
proof fn complex_conj_involution(c: Complex)
    ensures
        c.conj().conj() == c,
{
    let cc = c.conj().conj();
    assert(cc.real == c.real);
    assert(cc.imag == c.imag);
    assert(cc == c);
}

/* helper modified by LLM (iteration 5): conj equals when imag zero */
proof fn complex_conj_imag_zero(c: Complex)
    ensures
        c.imag == 0 ==> c.conj() == c,
{
    if c.imag == 0 {
        let cc = c.conj();
        assert(cc.real == c.real);
        assert(cc.imag == -c.imag);
        assert(-c.imag == c.imag);
        assert(cc == c);
    }
}

/* helper modified by LLM (iteration 5): norm squared invariant under conj */
proof fn complex_norm_sq_invariant(c: Complex)
    ensures
        c.norm_sq() == c.conj().norm_sq(),
{
    let cc = c.conj();
    assert(cc.real == c.real);
    assert(cc.imag == -c.imag);
    assert(cc.real * cc.real + cc.imag * cc.imag == c.real * c.real + (-c.imag) * (-c.imag));
    assert((-c.imag) * (-c.imag) == c.imag * c.imag);
    assert(cc.real * cc.real + cc.imag * cc.imag == c.real * c.real + c.imag * c.imag);
}

/* helper modified by LLM (iteration 5): conj distributes over add */
proof fn complex_add_conj(a: Complex, b: Complex)
    ensures
        (a.add(b)).conj() == a.conj().add(b.conj()),
{
    let lhs = (a.add(b)).conj();
    let rhs = a.conj().add(b.conj());
    assert(lhs.real == a.real + b.real);
    assert(lhs.imag == -(a.imag + b.imag));
    assert(rhs.real == a.real + b.real);
    assert(rhs.imag == -a.imag + -b.imag);
    assert(rhs.imag == -(a.imag + b.imag));
    assert(lhs == rhs);
}

/* helper modified by LLM (iteration 5): conj interacts with mul */
proof fn complex_mul_conj(a: Complex, b: Complex)
    ensures
        (a.mul(b)).conj() == a.conj().mul(b.conj()),
{
    let lhs = (a.mul(b)).conj();
    let rhs = a.conj().mul(b.conj());
    // lhs components
    assert(lhs.real == a.real * b.real - a.imag * b.imag);
    assert(lhs.imag == -(a.real * b.imag + a.imag * b.real));
    // rhs components
    assert(rhs.real == a.real * b.real - (-a.imag) * (-b.imag));
    assert(rhs.imag == a.real * (-b.imag) + (-a.imag) * b.real);
    assert((-a.imag) * (-b.imag) == a.imag * b.imag);
    assert(rhs.real == a.real * b.real - a.imag * b.imag);
    assert(rhs.imag == -a.real * b.imag - a.imag * b.real);
    assert(rhs.imag == -(a.real * b.imag + a.imag * b.real));
    assert(lhs == rhs);
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
    /* code modified by LLM (iteration 5): build conjugate vector */
    let n: int = x@.len();
    let mut res: Vec<Complex> = Vec::new();
    let mut i: int = 0;
    while i < n
        invariant
            0 <= i,
            i <= n,
            res@.len() == i,
            forall|j: int| 0 <= j && j < i ==> res@[j].real == x@[j].real && res@[j].imag == -x@[j].imag,
        decreases n - i
    {
        let xi: Complex = x@[i];
        let c = Complex { real: xi.real, imag: -xi.imag };
        res.push(c);
        i = i + 1;
    }

    res
}

// </vc-code>


}
fn main() {}