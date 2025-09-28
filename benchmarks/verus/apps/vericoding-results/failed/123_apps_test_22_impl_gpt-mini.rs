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
/* helper modified by LLM (iteration 5): predicate for palindrome characters */
spec fn is_pal_char(c: char) -> bool {
    let pal = seq!['A', 'H', 'I', 'M', 'O', 'o', 'T', 'U', 'V', 'v', 'W', 'w', 'X', 'x', 'Y'];
    pal.contains(c)
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
    /* code modified by LLM (iteration 5): runtime palindrome check using byte numeric literals */
    let bytes = s.as_bytes();
    let n = bytes.len();
    let mut i = 0usize;
    while i < n / 2
        invariant
            i <= n / 2,
    {
        let a = bytes[i];
        let b = bytes[n - 1 - i];
        if a == b {
            let is_pal = a == 65u8 || a == 72u8 || a == 73u8 || a == 77u8 || a == 79u8 || a == 111u8 || a == 84u8 || a == 85u8 || a == 86u8 || a == 118u8 || a == 87u8 || a == 119u8 || a == 88u8 || a == 120u8 || a == 89u8;
            if !is_pal {
                return String::from("NIE");
            }
        } else {
            if !((a == 112u8 && b == 113u8) || (a == 113u8 && b == 112u8) || (a == 98u8 && b == 100u8) || (a == 100u8 && b == 98u8)) {
                return String::from("NIE");
            }
        }
        i += 1;
    }
    String::from("TAK")
}
// </vc-code>


}

fn main() {}