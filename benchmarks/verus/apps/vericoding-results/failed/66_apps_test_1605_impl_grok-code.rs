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
/* helper modified by LLM (iteration 2): added exec versions */ fn merge_consecutive_exec(s: Seq<char>) -> Seq<char>
    decreases s.len()
{
    if s.len() == 0 {
        s
    } else if s.len() == 1 {
        s
    } else if s[0] == s[1] {
        merge_consecutive_exec(s.subrange(1, s.len() as int))
    } else {
        seq![s[0]].add(merge_consecutive_exec(s.subrange(1, s.len() as int)))
    }
}
 fn is_palindrome_exec(s: Seq<char>) -> bool
    decreases s.len()
{
    if s.len() <= 1 {
        true
    } else {
        s[0] == s[s.len() - 1] && is_palindrome_exec(s.subrange(1, s.len() - 1))
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: (u32, u32))
    requires valid_input(s@)
    ensures valid_output(s@, result.0 as int, result.1 as int)
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 2): fix syntax and implement */
let mut even_count: u32 = 0;
let mut odd_count: u32 = 0;
let n = s@.len();
let mut i: int = 0;
while i < n
invariant
0 <= i <= n,
even_count as int <= u32::MAX as int,
odd_count as int <= u32::MAX as int,
decreases n - i
{
let mut j: int = i;
while j < n
invariant
i <= j <= n,
even_count as int <= u32::MAX as int,
odd_count as int <= u32::MAX as int,
decreases n - j
{
let sub = s@.subrange(i, j + 1);
let merged = merge_consecutive_exec(sub);
if is_palindrome_exec(merged) {
let len_sub = (j - i) + 1;
if len_sub % 2 == 0 {
even_count = even_count + 1;
} else {
odd_count = odd_count + 1;
}
}
j = j + 1;
}
i = i + 1;
}
(even_count, odd_count)
}
// </vc-code>


}

fn main() {}