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
/* helper modified by LLM (iteration 5): use Vec::from_iter to build Vec from iterator */
fn string_to_vec(s: &str) -> (result: Vec<char>)
    ensures
        result@ == s@,
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result@.len() == i,
            forall|j: int| 0 <= j < i ==> result@[j] == s@[j],
    {
        result.push(s.get_char(i));
        i += 1;
    }
    result
}

/* helper modified by LLM (iteration 5): get character from Vec instead of str directly */
fn get_char_at(chars: &Vec<char>, i: usize) -> (result: char)
    requires
        i < chars@.len(),
    ensures
        result == chars@[i as int],
{
    chars[i]
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
    /* code modified by LLM (iteration 5): use manual iteration to build Vec instead of collect() */
    let chars_vec = string_to_vec(s);
    let chars: Seq<char> = chars_vec@;
    let pal = seq!['A', 'H', 'I', 'M', 'O', 'o', 'T', 'U', 'V', 'v', 'W', 'w', 'X', 'x', 'Y'];
    
    let mut i = 0;
    let len = chars_vec.len();
    
    while i < len / 2
        invariant
            0 <= i <= len / 2,
            len == chars.len(),
            chars == s@,
            forall|k: int| #![trigger chars[k]] 0 <= k < i ==> {
                let j = chars.len() - 1 - k;
                if chars[k] == chars[j] {
                    pal.contains(chars[k])
                } else {
                    (chars[k] == 'p' && chars[j] == 'q') || (chars[k] == 'q' && chars[j] == 'p') ||
                    (chars[k] == 'b' && chars[j] == 'd') || (chars[k] == 'd' && chars[j] == 'b')
                }
            },
    {
        let j = len - 1 - i;
        let char_i = get_char_at(&chars_vec, i);
        let char_j = get_char_at(&chars_vec, j);
        
        if char_i == char_j {
            if !pal.contains(char_i) {
                return "NIE".to_string();
            }
        } else {
            if !((char_i == 'p' && char_j == 'q') || (char_i == 'q' && char_j == 'p') ||
                 (char_i == 'b' && char_j == 'd') || (char_i == 'd' && char_j == 'b')) {
                return "NIE".to_string();
            }
        }
        
        i += 1;
    }
    
    "TAK".to_string()
}
// </vc-code>


}

fn main() {}