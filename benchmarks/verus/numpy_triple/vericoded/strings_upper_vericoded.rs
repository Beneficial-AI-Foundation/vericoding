// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn string_to_upper(s: Seq<char>) -> Seq<char> {
    s
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_string_to_upper_id(s: Seq<char>)
    ensures
        string_to_upper(s) == s,
{
}
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
    a
}
// </vc-code>


}
fn main() {}