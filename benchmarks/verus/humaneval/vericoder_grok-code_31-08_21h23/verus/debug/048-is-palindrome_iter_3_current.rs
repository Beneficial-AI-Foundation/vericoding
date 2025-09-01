use vstd::prelude::*;

verus! {

// <vc-helpers>
#[spec]
fn spec_index[T](s: Seq<T>, i: int) -> T
    requires 0 <= i < s.len(),
    decreases i,
{
    s[i]
}
// </vc-helpers>

// <vc-spec>
fn is_palindrome(text: &str) -> (result: bool)
    // post-conditions-start
    ensures
        result == forall|i: int|
            0 <= i < text@.len() ==> #[trigger] text@[i] == text@[text@.len() - 1 - i],
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    let len = text@.len();
    let mut i: usize = 0;
    while i < len / 2
        invariant
            0 <= (i as int) <= len / 2,
            forall|j: int| 0 <= j < (i as int) ==> text@[j] == text@[len - 1 - j],
    {
        if text@[i as int] != text@[len - 1 - (i as int)] {
            return false;
        }
        i = i + 1;
    }
    true
}
// </vc-code>

fn main() {}
}