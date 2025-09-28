// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn string_to_upper(s: Seq<char>) -> Seq<char> {
    s
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn upper(a: Vec<String>) -> (result: Vec<String>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() as int ==>
            result@[i]@ == string_to_upper(a@[i]@) &&
            result@[i]@.len() == a@[i]@.len()
// </vc-spec>
// <vc-code>
{
    let mut result: Vec<String> = Vec::new();
    let mut i: usize = 0;
    while i < a.len()
        invariant
            0 <= i <= a.len(),
            result.len() == i,
            forall|j: int| 0 <= j < i as int ==> result@[j]@ == string_to_upper(a@[j]@),
        decreases a.len() - i
    {
        let s_cloned = a[i].clone();
        result.push(s_cloned);
        i = i + 1;
    }
    result
}
// </vc-code>


}
fn main() {}