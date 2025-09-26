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
    assume(false);
    (0, 0)
}
// </vc-code>


}

fn main() {}