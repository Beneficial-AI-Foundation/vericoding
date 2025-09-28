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
/* helper modified by LLM (iteration 5): add exec palindrome checker helper */
fn is_palindrome(s: &str) -> (res: bool)
    ensures
        res <==> is_s_palindrome(s@),
{
    let chars: Vec<char> = s.chars().collect();
    let len = chars.len();
    let mut i = 0;
    while i < len / 2
        invariant
            0 <= i <= len / 2,
            forall|j: int| 0 <= j < i ==> {
                let k = len - 1 - j;
                if chars@[j] == chars@[k] {
                    let pal = seq!['A', 'H', 'I', 'M', 'O', 'o', 'T', 'U', 'V', 'v', 'W', 'w', 'X', 'x', 'Y'];
                    pal.contains(chars@[j])
                } else {
                    (chars@[j] == 'p' && chars@[k] == 'q') ||
                    (chars@[j] == 'q' && chars@[k] == 'p') ||
                    (chars@[j] == 'b' && chars@[k] == 'd') ||
                    (chars@[j] == 'd' && chars@[k] == 'b')
                }
            },
    {
        let j = i;
        let k = len - 1 - j;
        let si = chars[j];
        let sj = chars[k];
        let pal_chars = ['A', 'H', 'I', 'M', 'O', 'o', 'T', 'U', 'V', 'v', 'W', 'w', 'X', 'x', 'Y'];
        let mut is_pal_char = false;
        for p in pal_chars.iter() {
            if si == *p {
                is_pal_char = true;
                break;
            }
        }
        if si == sj {
            if !is_pal_char {
                return false;
            }
        } else {
            let valid_pair = (si == 'p' && sj == 'q') || (si == 'q' && sj == 'p') ||
                             (si == 'b' && sj == 'd') || (si == 'd' && sj == 'b');
            if !valid_pair {
                return false;
            }
        }
        i = i + 1;
    }
    true
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
{
    /* code modified by LLM (iteration 5): check if palindrome using helper and return appropriate string */
    if is_palindrome(s) {
        "TAK".to_string()
    } else {
        "NIE".to_string()
    }
}
// </vc-code>


}

fn main() {}