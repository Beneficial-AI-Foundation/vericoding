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
{
    /* code modified by LLM (iteration 5): Fixed nat to usize conversion using len() method directly */
    let pal = vec!['A', 'H', 'I', 'M', 'O', 'o', 'T', 'U', 'V', 'v', 'W', 'w', 'X', 'x', 'Y'];
    
    let mut i: usize = 0;
    let mut is_palindrome = true;
    let n = s.unicode_len();
    
    while i < n / 2
        invariant
            0 <= i <= n / 2,
            n == s@.len(),
            is_palindrome <==> forall|k: int| 0 <= k < i as int ==> {
                let j = s@.len() - 1 - k;
                if s@[k] == s@[j] {
                    pal@.contains(s@[k])
                } else {
                    (s@[k] == 'p' && s@[j] == 'q') || (s@[k] == 'q' && s@[j] == 'p') ||
                    (s@[k] == 'b' && s@[j] == 'd') || (s@[k] == 'd' && s@[j] == 'b')
                }
            },
    {
        let j = n - 1 - i;
        let c_i = s.get_char(i);
        let c_j = s.get_char(j);
        
        if c_i == c_j {
            let mut found = false;
            let mut k: usize = 0;
            while k < 15  // pal.len() is 15
                invariant
                    0 <= k <= 15,
                    k <= pal@.len(),
                    found <==> exists|m: int| 0 <= m < k as int ==> pal@[m] == c_i,
            {
                if pal[k] == c_i {
                    found = true;
                    break;
                }
                k = k + 1;
            }
            
            if !found {
                is_palindrome = false;
                break;
            }
        } else if (c_i == 'p' && c_j == 'q') || (c_i == 'q' && c_j == 'p') ||
                  (c_i == 'b' && c_j == 'd') || (c_i == 'd' && c_j == 'b') {
            // Valid pair
        } else {
            is_palindrome = false;
            break;
        }
        
        i = i + 1;
    }
    
    if is_palindrome {
        "TAK".to_string()
    } else {
        "NIE".to_string()
    }
}
// </vc-code>


}

fn main() {}