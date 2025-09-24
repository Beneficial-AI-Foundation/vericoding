// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn char_to_lower(c: char) -> char;

spec fn string_to_lower(s: Seq<char>) -> Seq<char>
    decreases s.len()
{
    if s.len() == 0 {
        seq![]
    } else {
        seq![char_to_lower(s[0])] + string_to_lower(s.skip(1))
    }
}

fn lower(a: Vec<Vec<char>>) -> (result: Vec<Vec<char>>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> #[trigger] result[i]@ == string_to_lower(a[i]@),
        forall|i: int| 0 <= i < a.len() ==> result[i].len() == a[i].len(),
        forall|i: int| 0 <= i < a.len() ==> (a[i].len() == 0 ==> result[i].len() == 0),
        forall|i: int| 0 <= i < a.len() ==> string_to_lower(result[i]@) == result[i]@,
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}
fn main() {}