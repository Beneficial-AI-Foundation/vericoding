// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, s: Seq<char>) -> bool {
    n == s.len() && n >= 0
}

spec fn is_good_string(s: Seq<char>) -> bool {
    s.len() % 2 == 0 && forall|i: int| 0 <= i < s.len() / 2 ==> #[trigger] s[2*i] != #[trigger] s[2*i+1]
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn solve(n: usize, s: Vec<char>) -> (result: (usize, Vec<char>))
    requires 
        valid_input(n as int, s@),
    ensures 
        result.0 >= 0,
        result.0 == s@.len() - result.1@.len(),
        is_good_string(result.1@),
        result.0 + result.1@.len() == s@.len(),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Fixed invariant logic for tracking processed vs remaining characters */
    let mut good_string: Vec<char> = Vec::new();
    let mut i: usize = 0;
    let mut removed: usize = 0;
    
    while i < n
        invariant
            0 <= i <= n,
            n == s@.len(),
            removed >= 0,
            is_good_string(good_string@),
            good_string@.len() % 2 == 0,
            i == good_string@.len() + removed,
        decreases n - i
    {
        if i + 1 < n && s[i] != s[i + 1] {
            good_string.push(s[i]);
            good_string.push(s[i + 1]);
            i = i + 2;
        } else {
            removed = removed + 1;
            i = i + 1;
        }
    }
    
    (removed, good_string)
}
// </vc-code>


}

fn main() {}