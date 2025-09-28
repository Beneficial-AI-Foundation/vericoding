// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(s: Seq<char>) -> bool {
    s.len() > 0 && forall|i: int| 0 <= i < s.len() ==> s[i] == 'a' || s[i] == 'b'
}

spec fn merge_consecutive(s: Seq<char>) -> Seq<char>
    decreases s.len()
{
    if s.len() == 0 {
        s
    } else if s.len() == 1 {
        s
    } else if s[0] == s[1] {
        merge_consecutive(s.subrange(1, s.len() as int))
    } else {
        seq![s[0]].add(merge_consecutive(s.subrange(1, s.len() as int)))
    }
}

spec fn is_palindrome(s: Seq<char>) -> bool
    decreases s.len()
{
    if s.len() <= 1 {
        true
    } else {
        s[0] == s[s.len() - 1] && is_palindrome(s.subrange(1, s.len() - 1))
    }
}

spec fn is_good_substring(s: Seq<char>, i: int, j: int) -> bool {
    &&& valid_input(s)
    &&& 0 <= i <= j < s.len()
    &&& {
        let sub = s.subrange(i, j + 1);
        is_palindrome(merge_consecutive(sub))
    }
}

spec fn valid_output(s: Seq<char>, even_count: int, odd_count: int) -> bool {
    &&& valid_input(s)
    &&& even_count >= 0
    &&& odd_count >= 0
    &&& even_count + odd_count >= s.len()
    &&& odd_count >= s.len()
    &&& (s.len() == 1 ==> even_count == 0 && odd_count == 1)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: (u32, u32))
    requires valid_input(s@)
    ensures valid_output(s@, result.0 as int, result.1 as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed arithmetic overflow and type conversion issues */
    let n = s.len();
    
    // Ensure n fits in u32 to avoid overflow
    assert(n <= u32::MAX as usize);
    
    // Calculate total substrings: n*(n+1)/2
    // Need to ensure no overflow
    assert(n <= (usize::MAX / 2));
    assert(n + 1 <= usize::MAX);
    assert(n * (n + 1) <= usize::MAX);
    let total_substrings = (n * (n + 1)) / 2;
    
    // Calculate odd length substrings
    let odd_count: u32 = if n % 2 == 1 {
        // If n is odd: ((n+1)/2)^2
        assert((n + 1) / 2 <= u32::MAX as usize);
        let half = ((n + 1) / 2) as u32;
        assert(half <= (u32::MAX / half));
        half * half
    } else {
        // If n is even: (n/2)*(n/2+1)
        assert(n / 2 <= u32::MAX as usize);
        let half = (n / 2) as u32;
        assert(half + 1 <= u32::MAX);
        assert(half <= (u32::MAX / (half + 1)));
        half * (half + 1)
    };
    
    // Calculate even length substrings
    assert(total_substrings <= u32::MAX as usize);
    let even_count: u32 = (total_substrings as u32) - odd_count;
    
    // Verify our counting satisfies the postconditions
    assert(even_count as int >= 0);
    assert(odd_count as int >= 0);
    assert(even_count as int + odd_count as int == total_substrings as int);
    assert(total_substrings >= n);
    assert(odd_count as int >= n as int);
    
    if n == 1 {
        assert(even_count == 0);
        assert(odd_count == 1);
    }
    
    (even_count, odd_count)
}
// </vc-code>


}

fn main() {}