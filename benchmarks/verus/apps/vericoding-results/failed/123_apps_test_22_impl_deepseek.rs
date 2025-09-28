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
/* helper modified by LLM (iteration 5): Fixed syntax error with inequality operator */
proof fn palindrome_lemma(s: Seq<char>, i: int)
    requires
        0 <= i < s.len(),
        is_s_palindrome(s),
    ensures
        let j = s.len() - 1 - i;
        i >= j || is_palindrome_char_pair(s[i], s[j])
{
    // Derivation from is_s_palindrome definition
    // is_s_palindrome(s) implies forall |k: int| 0 <= k < s.len() ==> [condition]
    // For this specific i, the condition must hold
    assert(is_s_palindrome(s));
}

spec fn is_palindrome_char_pair(c1: char, c2: char) -> bool {
    (c1 == c2 && seq!['A', 'H', 'I', 'M', 'O', 'o', 'T', 'U', 'V', 'v', 'W', 'w', 'X', 'x', 'Y'].contains(c1)) ||
    (c1 == 'p' && c2 == 'q') || (c1 == 'q' && c2 == 'p') ||
    (c1 == 'b' && c2 == 'd') || (c1 == 'd' && c2 == 'b')
}
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
/* code modified by LLM (iteration 5): Maintains while loop with proper invariant */
{
    let chars: Vec<char> = s.chars().collect();
    let len = chars.len();
    let mut i: usize = 0;
    let mut is_pal = true;
    
    while i < len / 2
        invariant
            0 <= i <= len / 2,
            is_pal <==> forall|k: int| 0 <= k < i ==> is_palindrome_char_pair(chars@[k], chars@[len - 1 - k])
    {
        let left_char = chars[i];
        let right_char = chars[len - 1 - i];
        
        if !is_palindrome_char_pair(left_char, right_char) {
            is_pal = false;
            break;
        }
        
        i += 1;
    }
    
    if is_pal {
        "TAK".to_string()
    } else {
        "NIE".to_string()
    }
}
// </vc-code>


}

fn main() {}