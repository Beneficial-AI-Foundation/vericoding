// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn char_swapcase(c: char) -> char;

spec fn string_swapcase(s: Seq<char>) -> Seq<char>
    decreases s.len()
{
    if s.len() == 0 {
        Seq::<char>::empty()
    } else {
        seq![char_swapcase(s[0])] + string_swapcase(s.skip(1))
    }
}

fn swapcase(a: Vec<String>) -> (result: Vec<String>)
    ensures
        result.len() == a.len(),
        forall|i: int| 0 <= i < a.len() ==> result[i]@.len() == a[i]@.len(),
        forall|i: int, j: int| 0 <= i < a.len() && 0 <= j < a[i]@.len() ==> 
            #[trigger] result[i]@[j] == char_swapcase(a[i]@[j])
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>

}
fn main() {}