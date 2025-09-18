// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): boolean OR commutativity */
proof fn lemma_or_commutative(a: bool, b: bool)
    ensures (a || b) == (b || a)
{ }

/* helper modified by LLM (iteration 3): OR with false is identity */
proof fn lemma_or_false_identity(a: bool)
    ensures (a || false) == a
{ }

/* helper modified by LLM (iteration 3): OR with true yields true */
proof fn lemma_or_true_is_true(a: bool)
    ensures (a || true) == true
{ }

/* helper modified by LLM (iteration 3): OR idempotent */
proof fn lemma_or_idempotent(a: bool)
    ensures (a || a) == a
{ }

/* helper modified by LLM (iteration 3): if either is true, OR is true */
proof fn lemma_or_true_intro(a: bool, b: bool)
    ensures (a == true || b == true) ==> (a || b) == true
{ }

/* helper modified by LLM (iteration 3): if both false, OR is false */
proof fn lemma_or_both_false(a: bool, b: bool)
    ensures (a == false && b == false) ==> (a || b) == false
{ }
// </vc-helpers>

// <vc-spec>
fn logical_or(x1: Vec<bool>, x2: Vec<bool>) -> (result: Vec<bool>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x1[i] || x2[i]),

        forall|i: int| 0 <= i < result.len() ==> (x1[i] || x2[i]) == (x2[i] || x1[i]),

        forall|i: int| 0 <= i < result.len() ==> (x1[i] || false) == x1[i],

        forall|i: int| 0 <= i < result.len() ==> (x1[i] || true) == true,

        forall|i: int| 0 <= i < result.len() ==> (x1[i] || x1[i]) == x1[i],

        forall|i: int| 0 <= i < result.len() ==> (x1[i] == true || x2[i] == true) ==> result[i] == true,

        forall|i: int| 0 <= i < result.len() ==> (x1[i] == false && x2[i] == false) ==> result[i] == false,
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): fixed while-invariant placement and implemented element-wise OR */
    let n = x1.len();
    let mut res: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant x1.len() == n && x2.len() == n &&
                  res.len() == i &&
                  i <= n &&
                  forall|j: int| 0 <= j && j < i as int ==> res[j] == (x1[j] || x2[j])
        decreases n as int - i as int
    {
        let b = x1[i] || x2[i];
        res.push(b);
        i = i + 1;
    }
    res
}
// </vc-code>

}
fn main() {}