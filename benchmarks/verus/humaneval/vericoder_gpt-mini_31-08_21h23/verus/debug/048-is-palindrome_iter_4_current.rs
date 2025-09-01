use vstd::prelude::*;

verus! {

// <vc-helpers>
// No helper functions needed for this example
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
    let s: Seq<char> = text@;
    let n: nat = s.len();
    let ok: bool = forall|i: int|
        0 <= i && i < (n as int) ==>
            #[trigger] s@[i as nat] == s@[(n - 1 - (i as nat))];
    ok
}
// </vc-code>

fn main() {}
}