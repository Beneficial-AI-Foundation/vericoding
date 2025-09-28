// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_titlecased(s: Seq<char>) -> bool;
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): map a sequence of strings (as Seq<Seq<char>>) to Seq<bool> using is_titlecased */
spec fn map_is_titlecased(strings: Seq<Seq<char>>) -> Seq<bool>
{
    Seq::new(strings.len(), |i: int| is_titlecased(strings[i]))
}
// </vc-helpers>

// <vc-spec>
fn istitle(a: Vec<String>) -> (result: Vec<bool>)
    ensures 
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i] == is_titlecased(a[i]@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): build ghost sequence of results and materialize with Vec::from_seq */
    let n = a.len();
    let ghost sres: Seq<bool> = Seq::new(n as nat, |i: int| is_titlecased((a@[i])@));
    let res: Vec<bool> = Vec::from_seq(sres);
    res
}
// </vc-code>

}
fn main() {}