// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_palindrome(s: Seq<char>) -> bool {
    forall|k: int| #![trigger s.index(k)] 0 <= k < s.len() ==> s.index(k) == s.index(s.len() - 1 - k)
}

spec fn starts_with(result: Seq<char>, s: Seq<char>) -> bool {
    result.len() >= s.len() && forall|k: int| #![trigger result.index(k)] 0 <= k < s.len() ==> result.index(k) == s.index(k)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn make_palindrome(s: &str) -> (result: String)
    ensures 
        result@.len() <= 2 * s@.len(),
        is_palindrome(result@),
        starts_with(result@, s@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fix int conversions - use usize arithmetic only in executable code */
    let n = s.unicode_len();
    
    // Find the longest suffix that is a palindrome
    let mut suffix_start: usize = 0;
    let mut i: usize = 0;
    
    while i < n
        invariant
            i <= n,
            suffix_start <= i,
            forall|j: int| 0 <= j < suffix_start ==> !is_palindrome(s@.subrange(j as int, n as int)),
    {
        // Check if substring from i to end is a palindrome
        let mut is_palin = true;
        let mut k: usize = 0;
        let substr_len = n - i;
        
        while k < substr_len / 2
            invariant
                k <= substr_len / 2,
                substr_len == n - i,
                i < n,
                is_palin == (forall|m: int| 0 <= m < k as int ==> s@.index(i as int + m) == s@.index((n - 1 - m) as int)),
        {
            let left_idx = i + k;
            let right_idx = n - 1 - k;
            
            if s.get_char(left_idx) != s.get_char(right_idx) {
                is_palin = false;
                k = substr_len / 2; // Exit loop
            } else {
                k = k + 1;
            }
        }
        
        if is_palin {
            suffix_start = i;
            i = n; // Exit outer loop
        } else {
            i = i + 1;
        }
    }
    
    // Build palindrome string
    let mut result = s.to_string();
    
    if suffix_start > 0 {
        let mut j: usize = suffix_start - 1;
        loop
            invariant
                j < suffix_start,
                result@.len() == s@.len() + (suffix_start - 1 - j) as int,
                forall|k: int| 0 <= k < s@.len() ==> result@.index(k) == s@.index(k),
                forall|k: int| s@.len() <= k < result@.len() ==> result@.index(k) == s@.index(suffix_start as int - 1 - (k - s@.len())),
            decreases j
        {
            // Push character at position j
            let ch = s.get_char(j);
            result.push(ch);
            if j == 0 {
                break;
            }
            j = j - 1;
        }
    }
    
    result
}
// </vc-code>


}

fn main() {}