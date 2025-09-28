// <vc-preamble>
use vstd::prelude::*;
use vstd::string::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed duplicate string_compare_gt; added benign helper */

spec fn seq_len_ge(s: Seq<char>, n: nat) -> bool {
    s.len() >= n
}
// </vc-helpers>

// <vc-spec>
spec fn string_compare_gt(s1: Seq<char>, s2: Seq<char>) -> bool {
    true  // placeholder implementation
}

fn greater(x1: &Vec<String>, x2: &Vec<String>) -> (result: Vec<bool>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),

        forall|i: int| 0 <= i < result.len() as int ==> 
            result[i] == string_compare_gt(x1[i]@, x2[i]@),

        forall|i: int| 0 <= i < result.len() as int ==> 
            result[i] ==> !string_compare_gt(x2[i]@, x1[i]@),

        forall|i: int| 0 <= i < result.len() as int ==> 
            (x1[i]@ == x2[i]@) ==> (result[i] == false),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): compute runtime lexicographic comparison using Vec<String> ordering */
    let len = x1.len();
    let mut result: Vec<bool> = Vec::new();
    let mut i: usize = 0;
    while i < len
        invariant
            i <= len,
            result.len() == i,
        decreases len - i
    {
        let b = x1[i] > x2[i];
        result.push(b);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}