// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_length(s: Seq<char>) -> bool {
    s.len() >= 3
}

spec fn all_windows_distinct(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i <= s.len() - 3 ==> #[trigger] s[i] != s[i+1] && s[i] != s[i+2] && s[i+1] != s[i+2]
}

spec fn is_happy_spec(s: Seq<char>) -> bool {
    valid_length(s) && all_windows_distinct(s)
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn is_happy(s: Vec<char>) -> (result: bool)
    ensures result == is_happy_spec(s@)
// </vc-spec>
// <vc-code>
{
    if s.len() < 3 {
        return false;
    }
    
    let mut i = 0;
    while i <= s.len() - 3
        invariant
            0 <= i <= s.len() - 3 + 1,
            s.len() >= 3,
            forall|j: int| 0 <= j < i ==> #[trigger] s@[j] != s@[j+1] && s@[j] != s@[j+2] && s@[j+1] != s@[j+2],
        decreases s.len() - i
    {
        if s[i] == s[i+1] || s[i] == s[i+2] || s[i+1] == s[i+2] {
            return false;
        }
        i += 1;
    }
    
    true
}
// </vc-code>


}

fn main() {}