// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn is_palindrome(text: &str) -> (result: bool)

    ensures
        result == forall|i: int|
            0 <= i < text@.len() ==> #[trigger] text@[i] == text@[text@.len() - 1 - i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed compilation error by using chars().collect() and chars.len() for runtime char count */
    let chars: Vec<char> = text.chars().collect::<Vec<_>>();
    let n: usize = chars.len();
    let mut i: usize = 0;
    while i < n / 2
        invariant
            0 <= i <= (n / 2),
            forall |j: int| 0 <= j < i ==>
                #[trigger] text@[j as int] == text@[n as int - 1 - j as int],
        decreases (n as int - i),
    {
        if chars[i] != chars[(n - 1 - i)] {
            return false;
        }
        i = i + 1;
    }
    true
}
// </vc-code>

}
fn main() {}