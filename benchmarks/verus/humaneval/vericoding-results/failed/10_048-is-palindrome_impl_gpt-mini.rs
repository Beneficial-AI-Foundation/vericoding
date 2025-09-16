// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): expose spec sequence of a string */
spec fn seq_of_str(s: &str) -> Seq<char> { s@ }
// </vc-helpers>

// <vc-spec>
fn is_palindrome(text: &str) -> (result: bool)

    ensures
        result == forall|i: int|
            0 <= i < text@.len() ==> #[trigger] text@[i] == text@[text@.len() - 1 - i],
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): runtime palindrome check with proof relating to spec */
    let chars: Vec<char> = text.chars().collect();
    let n: usize = chars.len();
    let mut i: usize = 0;
    let mut ok: bool = true;
    while i < n / 2
        invariant
            i <= n,
        decreases n - i
    {
        if chars[i] != chars[n - 1 - i] {
            ok = false;
            break;
        }
        i += 1;
    }
    let result = ok;
    proof {
        let tracked seq: Seq<char> = seq_of_str(text);
        let tracked len: int = seq.len() as int;
        // If result is true then every corresponding pair matches
        assert((result == true) ==> (forall|k: int| 0 <= k < len ==> seq@[k as nat] == seq@((len - 1 - k) as nat)));
        // If result is false then the universal property does not hold
        assert((result == false) ==> !(forall|k: int| 0 <= k < len ==> seq@[k as nat] == seq@((len - 1 - k) as nat))));
        // Combine to conclude equality
        assert(result == (forall|k: int| 0 <= k < len ==> seq@[k as nat] == seq@((len - 1 - k) as nat))));
    }
    result
}
// </vc-code>

}
fn main() {}