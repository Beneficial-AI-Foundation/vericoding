use vstd::prelude::*;

verus! {

fn is_palindrome(text: &str) -> (result: bool)

    ensures
        result == forall|i: int|
            0 <= i < text@.len() ==> #[trigger] text@[i] == text@[text@.len() - 1 - i],
{
    assume(false);
    unreached();
}

}
fn main() {}