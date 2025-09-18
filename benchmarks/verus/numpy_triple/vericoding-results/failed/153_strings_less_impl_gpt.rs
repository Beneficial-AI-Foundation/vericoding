// <vc-preamble>
use vstd::prelude::*;
use vstd::string::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): define lexicographic less-than on sequences of chars */
pub open spec fn lex_lt(a: Seq<char>, b: Seq<char>) -> bool
    decreases a.len() + b.len()
{
    if a.len() == 0 {
        b.len() > 0
    } else if b.len() == 0 {
        false
    } else if a.first() < b.first() {
        true
    } else if a.first() > b.first() {
        false
    } else {
        lex_lt(a.drop_first(), b.drop_first())
    }
}
// </vc-helpers>

// <vc-spec>
spec fn str_less_than(s1: String, s2: String) -> bool;

fn less(x1: Vec<String>, x2: Vec<String>) -> (result: Vec<bool>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),

        forall|i: int| 0 <= i < result.len() ==> result[i] == str_less_than(x1[i], x2[i]),

        forall|i: int| 0 <= i < result.len() && result[i] == true ==> !str_less_than(x2[i], x1[i]),

        forall|i: int| 0 <= i < result.len() && x1[i] == x2[i] ==> result[i] == false,

        forall|i: int| 0 <= i < result.len() ==> result[i] == true || result[i] == false,

        forall|i: int| 0 <= i < result.len() && result[i] == true ==> x1[i] != x2[i],

        forall|i: int| 0 <= i < result.len() ==> result[i] == true || x1[i] == x2[i] || str_less_than(x2[i], x1[i])
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute elementwise strict string order using < and maintain spec mapping invariant */
    let n = x1.len();
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < n
        invariant
            i <= n,
            result.len() == i,
            forall|j: int| 0 <= j < i ==> result[j] == str_less_than(x1[j], x2[j]),
        decreases (n as int) - (i as int)
    {
        let b = x1[i] < x2[i];
        result.push(b);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}