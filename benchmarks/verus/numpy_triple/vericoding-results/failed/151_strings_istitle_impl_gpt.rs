// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_titlecased(s: Seq<char>) -> bool;
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): spec builder for mapping is_titlecased over a sequence of strings (as sequences of chars) */
spec fn map_istitle(a: Seq<Seq<char>>) -> Seq<bool> { Seq::new(a.len(), |i: int| is_titlecased(a[i])) }
// </vc-helpers>

// <vc-spec>
fn istitle(a: Vec<String>) -> (result: Vec<bool>)
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == is_titlecased(a[i]@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): construct result from spec sequence mapping is_titlecased over input strings */
    let n = a.len();
    let s: Seq<bool> = Seq::new(n as nat, |i: int| is_titlecased(a@[i]@));
    let result: Vec<bool> = Vec::from_seq(s);
    result
}
// </vc-code>

}
fn main() {}