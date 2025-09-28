// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn is_upper_case(c: char) -> bool {
    65 <= c as int <= 90
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn count_uppercase(s: &str) -> (count: usize)
    ensures 
        count >= 0,
        count as int == s@.filter(|c: char| is_upper_case(c)).len(),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): changed loop counter from ghost 'int' to executable 'usize' to fix compilation error */
{
    let mut count: usize = 0;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            i <= s.len(),
            count as int == s@.subrange(0, i as int).filter(|c: char| is_upper_case(c)).len(),
        decreases s.len() - i
    {
        let c = s.get_char(i);
        if is_upper_case(c) {
            count = count + 1;
        }
        i = i + 1;
    }
    count
}
// </vc-code>

}
fn main() {}