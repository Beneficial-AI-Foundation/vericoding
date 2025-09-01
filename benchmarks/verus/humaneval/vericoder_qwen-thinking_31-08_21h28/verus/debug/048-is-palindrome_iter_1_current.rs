use vstd::prelude::*;

verus! {

// <vc-helpers>
lemma palindrome_invariant_implies_full(n: nat, text: Seq<char>)
    ensures
        (forall j: int :: 0 <= j < n.to_int()/2 ==> #[trigger] (text[j] == text[n.to_int()-1-j]))
            ==>
        (forall i: int :: 0 <= i < n.to_int() ==> text[i] == text[n.to_int()-1-i])
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
    let n = text@.len();
    let mut i = 0;
    while i < n / 2 {
        invariant {
            (forall j: nat :: 0 <= j < i ==> #[trigger] (text@[j] == text@[n-1-j]))
        }
        if text@[i] != text@[n-1-i] {
            return false;
        }
        i = i + 1;
    }
    true
}
// </vc-code>

fn main() {}
}