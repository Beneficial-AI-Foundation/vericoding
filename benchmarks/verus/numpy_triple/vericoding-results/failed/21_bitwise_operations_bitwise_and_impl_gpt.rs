// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added exec helper and a lemma about nonnegativity of bitwise AND for nonnegative operands */
fn bit_and_i32(a: i32, b: i32) -> i32 { a & b }

proof fn lemma_bitand_nonneg(a: i32, b: i32)
    requires
        a >= 0,
        b >= 0
    ensures
        (a & b) >= 0
{ }
// </vc-helpers>

// <vc-spec>
fn bitwise_and(x1: Vec<i32>, x2: Vec<i32>) -> (result: Vec<i32>)
    requires 
        x1.len() == x2.len(),
        forall|i: int| 0 <= i < x1.len() ==> x1[i] >= 0,
        forall|i: int| 0 <= i < x2.len() ==> x2[i] >= 0,
    ensures
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x1[i] & x2[i]),
        forall|i: int| 0 <= i < result.len() ==> result[i] >= 0,
        forall|i: int| 0 <= i < result.len() ==> result[i] <= x1[i],
        forall|i: int| 0 <= i < result.len() ==> result[i] <= x2[i],
        forall|i: int| 0 <= i < result.len() ==> (result[i] == 0 <==> (x1[i] == 0 || x2[i] == 0)),
        forall|i: int| 0 <= i < result.len() ==> (x1[i] == x2[i] ==> result[i] == x1[i]),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): added loop invariants for element-wise bitwise AND and nonnegativity; asserted index safety */
    let n = x1.len();
    let mut out: Vec<i32> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            n == x1.len(),
            n == x2.len(),
            i <= n,
            out.len() == i,
            forall|j: int| 0 <= j < i as int ==> out@[j] == (x1[j] & x2[j]),
            forall|j: int| 0 <= j < i as int ==> out@[j] >= 0
        decreases n - i
    {
        assert(i < x1.len());
        assert(i < x2.len());
        let a = x1[i];
        let b = x2[i];
        assert(a >= 0);
        assert(b >= 0);
        let c = bit_and_i32(a, b);
        assert(c == (a & b));
        lemma_bitand_nonneg(a, b);
        assert((a & b) >= 0);
        out.push(c);
        i += 1;
    }
    out
}
// </vc-code>

}
fn main() {}