// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn to_lower(c: char) -> char {
    if 'A' <= c && c <= 'Z' {
        ((c as u8 - 'A' as u8 + 'a' as u8) as char)
    } else {
        c
    }
}

spec fn is_palindrome_spec(text: Seq<char>) -> bool {
    forall|i: int| 0 <= i < text.len() ==> #[trigger] to_lower(text[i]) == to_lower(text[text.len() - 1 - i])
}
// </vc-preamble>

// <vc-helpers>
fn to_lower_exec(c: char) -> (res: char)
    ensures
        res == to_lower(c),
{
    if 'A' <= c && c <= 'Z' {
        ((c as u8 - 'A' as u8 + 'a' as u8) as char)
    } else {
        c
    }
}

/* helper modified by LLM (iteration 2): [reviewed lemma proof] */
proof fn lemma_palindrome_mirror(text: Seq<char>)
    requires
        forall|i: int| 0 <= i < text.len() / 2 ==> #[trigger] to_lower(text[i]) == to_lower(text[text.len() - 1 - i]),
    ensures
        is_palindrome_spec(text),
{
    let n = text.len();
    assert forall|k: int| 0 <= k < n implies #[trigger] to_lower(text[k]) == to_lower(text[n - 1 - k]) by {
        if k >= n / 2 {
            let k_mirror = n - 1 - k;
            assert(to_lower(text[k_mirror]) == to_lower(text[n - 1 - k_mirror]));
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn is_palindrome(text: Vec<char>) -> (result: bool)
    ensures result <==> is_palindrome_spec(text@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): [call lemma in proof block and add proofs for postconditions] */
    let n = text.len();
    let mut i: usize = 0;
    while i < n / 2
        invariant
            n == text.len(),
            0 <= i <= (n / 2),
            forall|j: int| 0 <= j < i ==> #[trigger] to_lower(text@[j]) == to_lower(text@[n - 1 - j]),
        decreases (n / 2) - i
    {
        if to_lower_exec(text[i]) != to_lower_exec(text[n - 1 - i]) {
            proof {
                assert(to_lower(text@[i as int]) != to_lower(text@[n - 1 - (i as int)]));
                assert(!is_palindrome_spec(text@));
            }
            return false;
        }
        i = i + 1;
    }

    proof {
        lemma_palindrome_mirror(text@);
        assert(is_palindrome_spec(text@));
    }
    return true;
}
// </vc-code>


}

fn main() {}