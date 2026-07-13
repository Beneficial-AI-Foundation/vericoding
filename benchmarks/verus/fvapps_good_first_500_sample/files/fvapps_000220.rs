// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn count_subsequences_spec(s: Seq<char>, t: Seq<char>) -> nat
    decreases s.len() + t.len()
{
    if t.len() == 0 {
        1
    } else if s.len() == 0 {
        0
    } else if s[0] == t[0] {
        count_subsequences_spec(s.skip(1), t.skip(1)) + count_subsequences_spec(s.skip(1), t)
    } else {
        count_subsequences_spec(s.skip(1), t)
    }
}

fn count_distinct_subsequences(s: &str, t: &str) -> (result: u32)
    ensures result as nat == count_subsequences_spec(s@, t@)
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    0
    // impl-end
}
// </vc-code>


}

fn main() {
    // println!("{}", count_distinct_subsequences("rabbbit", "rabbit"));
    // println!("{}", count_distinct_subsequences("babgbag", "bag"));
    // println!("{}", count_distinct_subsequences("abc", "abc"));
}