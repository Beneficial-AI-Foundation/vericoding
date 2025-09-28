// <vc-preamble>
use vstd::prelude::*;

verus! {

struct Complex {

    real: f64,

    imag: f64,
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added spec function for sequence mapping */
spec fn seq_is_complex(s: Seq<Complex>) -> Seq<bool>
    decreases s.len()
{
    if s.len() == 0 {
        Seq::new()
    } else {
        seq_is_complex(s.subrange(0, s.len() - 1)).push(s.last().imag != 0.0)
    }
}

/* helper modified by LLM (iteration 5): added lemma to prove spec function correctness */
proof fn lemma_seq_is_complex_is_correct(s: Seq<Complex>)
    ensures
        seq_is_complex(s).len() == s.len(),
        forall|i: int| 0 <= i < s.len() ==> seq_is_complex(s)@[i] == (s@[i].imag != 0.0),
    decreases s.len()
{
    if s.len() > 0 {
        lemma_seq_is_complex_is_correct(s.subrange(0, s.len() - 1));
    }
}
// </vc-helpers>

// <vc-spec>
fn is_complex(x: &Vec<Complex>) -> (result: Vec<bool>)
    ensures
        result.len() == x.len(),
        forall|i: int| 0 <= i < x@.len() ==> result@[i] == (x@[i].imag != 0.0),
        forall|i: int| 0 <= i < x@.len() ==> (x@[i].imag == 0.0 ==> result@[i] == false),
        forall|i: int| 0 <= i < x@.len() ==> (x@[i].imag != 0.0 ==> result@[i] == true),
        forall|i: int| 0 <= i < x@.len() ==> (result@[i] == true ==> x@[i].imag != 0.0),
        forall|i: int| 0 <= i < x@.len() ==> (result@[i] == false ==> x@[i].imag == 0.0)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): used a recursive spec function in loop invariant and called lemma */
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < x.len()
        invariant
            0 <= i <= x.len(),
            result.len() == i,
            result@ == seq_is_complex(x@.subrange(0, i as int)),
        decreases x.len() - i
    {
        let is_c = x[i].imag != 0.0;
        result.push(is_c);
        i = i + 1;
    }
    lemma_seq_is_complex_is_correct(x@);
    result
}
// </vc-code>

}
fn main() {}