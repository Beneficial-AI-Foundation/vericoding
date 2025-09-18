// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): trivial spec identity helper to avoid exec int usage */
spec fn id_bool(b: bool) -> bool { b }
// </vc-helpers>

// <vc-spec>
fn not_equal(x1: Vec<String>, x2: Vec<String>) -> (result: Vec<bool>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == (x1[i] != x2[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): construct result via ghost Seq and convert with Vec::from_seq */
    let n = x1.len();
    ghost let s1: Seq<String> = x1@;
    ghost let s2: Seq<String> = x2@;
    ghost let s: Seq<bool> = Seq::new(n as nat, |i: int| s1[i] != s2[i]);
    let result: Vec<bool> = Vec::from_seq(s);
    result
}
// </vc-code>

}
fn main() {}