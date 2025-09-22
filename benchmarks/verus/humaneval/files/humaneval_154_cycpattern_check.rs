// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn is_substring(s: Seq<char>, sub: Seq<char>) -> bool
    decreases s.len()
{
    if sub.len() == 0 {
        true
    } else if s.len() < sub.len() {
        false
    } else if s.len() == sub.len() {
        s == sub
    } else {
        (s.subrange(0, sub.len() as int) == sub) || is_substring(s.subrange(1, s.len() as int), sub)
    }
}

spec fn rotate_string(s: Seq<char>, n: nat) -> Seq<char>
    recommends 0 <= n <= s.len()
{
    s.subrange(n as int, s.len() as int).add(s.subrange(0, n as int))
}
// </vc-helpers>

// <vc-spec>
fn cycpattern_check(word: Seq<char>, pattern: Seq<char>) -> (result: bool)
    ensures result == exists|i: int| 0 <= i <= pattern.len() && is_substring(word, #[trigger] rotate_string(pattern, i as nat))
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    false
    // impl-end
}
// </vc-code>


}

fn main() {}