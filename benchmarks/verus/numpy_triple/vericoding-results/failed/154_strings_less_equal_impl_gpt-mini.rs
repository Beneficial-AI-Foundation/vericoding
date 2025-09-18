// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): lexicographic comparison of String using their sequences */
spec fn string_le(s1: String, s2: String) -> bool {
    let a = s1@;
    let b = s2@;
    (exists |k: nat| k < a.len() && k < b.len() && (forall |i: nat| i < k ==> a@[i] == b@[i]) && a@[k] < b@[k]) ||
    (a.len() <= b.len() && (forall |i: nat| i < a.len() ==> a@[i] == b@[i]))
}
// </vc-helpers>

// <vc-spec>
spec fn string_le(s1: String, s2: String) -> bool;

fn less_equal(x1: Vec<String>, x2: Vec<String>) -> (result: Vec<bool>)
    requires x1.len() == x2.len(),
    ensures 
        result.len() == x1.len(),
        forall|i: int| 0 <= i < result.len() ==> result[i] == string_le(x1[i], x2[i]),
        forall|i: int| 0 <= i < result.len() ==> (result[i] == true <==> string_le(x1[i], x2[i])),
        x1@ == x2@ ==> forall|i: int| 0 <= i < result.len() ==> result[i] == true,
        forall|i: int| 0 <= i < result.len() ==> (string_le(x1[i], x2[i]) && string_le(x2[i], x1[i])) ==> x1[i] == x2[i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): iterate over vectors and compute string_le for each pair */
    let mut result: Vec<bool> = Vec::new();
    let n = x1.len();
    let mut i: nat = 0;
    while i < n
        invariant i <= n,
        invariant result.len() == i,
        invariant forall |j: nat| j < i ==> result[j] == string_le(x1[j], x2[j]),
        decreases n - i
    {
        let b = string_le(x1[i], x2[i]);
        result.push(b);
        i = i + 1;
    }
    result
}
// </vc-code>

}
fn main() {}