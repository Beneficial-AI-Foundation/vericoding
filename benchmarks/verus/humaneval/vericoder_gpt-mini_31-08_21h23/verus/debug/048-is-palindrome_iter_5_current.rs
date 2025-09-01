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
    let mut chars: Vec<char> = Vec::new();
    // Collect characters of the string into a Vec<char>
    for c in text.chars() {
        chars.push(c);
    }

    let n: usize = chars.len();
    let mut i: usize = 0;
    let half: usize = n / 2;

    while i < half
        invariant chars@.len() == (n as nat)
        invariant forall|j: int|
            0 <= j && j < (i as int) ==>
                #[trigger] chars@[j as nat] == chars@[((n as int) - 1 - j) as nat]
    {
        if chars.get(i) != chars.get(n - 1 - i) {
            return false;
        }
        i += 1;
    }

    true
}
// </vc-code>

fn main() {}
}