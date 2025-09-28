// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn is_s_palindrome(s: Seq<char>) -> bool {
    let pal = seq!['A', 'H', 'I', 'M', 'O', 'o', 'T', 'U', 'V', 'v', 'W', 'w', 'X', 'x', 'Y'];
    
    forall|i: int| #![trigger s[i]] 0 <= i < s.len() ==> {
        let j = s.len() - 1 - i;
        if i >= j {
            true
        } else {
            if s[i] == s[j] {
                pal.contains(s[i])
            } else {
                (s[i] == 'p' && s[j] == 'q') || (s[i] == 'q' && s[j] == 'p') ||
                (s[i] == 'b' && s[j] == 'd') || (s[i] == 'd' && s[j] == 'b')
            }
        }
    }
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(s: &str) -> (result: String)
    requires
        s@.len() >= 1,
    ensures
        result@ == seq!['T', 'A', 'K'] || result@ == seq!['N', 'I', 'E'],
        (result@ == seq!['T', 'A', 'K']) <==> is_s_palindrome(s@),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): The `is_s_palindrome` function is a `spec` function and cannot be called directly in `exec` code. We need to create a `proof` block for evaluation and convert the char sequence to string.*/
{
    proof {
        if is_s_palindrome(s@) {
            assert(is_s_palindrome(s@));
        }
    }
    if is_s_palindrome(s@) {
        "TAK".to_string()
    } else {
        "NIE".to_string()
    }
}
// </vc-code>


}

fn main() {}