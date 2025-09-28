// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int, s: Seq<char>) -> bool {
    n == s.len() && n >= 1
}

spec fn count_distinct_chars(s: Seq<char>) -> int {
    s.to_set().len() as int
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): changed return type to nat to fix compilation with usize and allow casting to i32 in code */
fn count_distinct(s: Vec<char>) -> (result: nat)
    ensures
        result == count_distinct_chars(s@),
{
    let mut seen = vstd::set::Set::<char>::empty();
    let mut i = 0;
    let len = s.len();
    while i < len
        invariant
            i as int <= s@.len(),
            seen =~= s@.subrange(0, i as int).to_set(),
        decreases len as int - i as int,
    {
        if !seen.contains(s[i]) {
            seen.insert(s[i]);
        }
        i += 1;
    }
    seen.len()
}
// </vc-helpers>

// <vc-spec>
fn solve(n: usize, s: Vec<char>) -> (result: i32)
    requires 
        valid_input(n as int, s@)
    ensures 
        n > 26 ==> result == -1,
        n <= 26 ==> result >= 0 && result < n as i32,
        n <= 26 ==> result == s@.len() as i32 - count_distinct_chars(s@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed non-primitive cast by using nat return from helper, now can cast to i32 */
{
    let distinct = count_distinct(s);
    if n > 26 {
        -1
    } else {
        (n as i32) - (distinct as i32)
    }
}
// </vc-code>


}

fn main() {}