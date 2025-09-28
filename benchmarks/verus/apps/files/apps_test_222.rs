// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn generate_squares() -> Seq<int> {
    generate_squares_helper(1, 44721)
}

spec fn is_subsequence(pattern: Seq<char>, text: Seq<char>) -> bool {
    is_subsequence_helper(pattern, text, 0, 0)
}

spec fn int_to_string(n: int) -> Seq<char> {
    if n == 0 { seq!['0'] }
    else { int_to_string_helper(n) }
}

spec fn generate_squares_helper(start: int, end: int) -> Seq<int>
    decreases end + 1 - start when start <= end
{
    if start > end { Seq::empty() }
    else { seq![start * start].add(generate_squares_helper(start + 1, end)) }
}

spec fn is_subsequence_helper(pattern: Seq<char>, text: Seq<char>, pi: int, ti: int) -> bool
    decreases pattern.len() - pi + text.len() - ti when pi <= pattern.len() && ti <= text.len()
{
    if pi >= pattern.len() { true }
    else if ti >= text.len() { false }
    else if pattern[pi] == text[ti] { 
        is_subsequence_helper(pattern, text, pi + 1, ti + 1)
    } else {
        is_subsequence_helper(pattern, text, pi, ti + 1)
    }
}

spec fn int_to_string_helper(n: int) -> Seq<char>
    decreases n when n > 0
{
    if n < 10 { seq![('0' as u8 + (n % 10) as u8) as char] }
    else { int_to_string_helper(n / 10).add(seq![('0' as u8 + (n % 10) as u8) as char]) }
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: i32)
    requires 
        s.len() > 0,
        forall|i: int| 0 <= i < s.len() ==> '0' <= #[trigger] s@[i] <= '9',
        s@[0] != '0' || s.len() == 1,
    ensures 
        result == -1 || result >= 0,
        result == -1 ==> forall|sq: int| #[trigger] generate_squares().contains(sq) ==> !is_subsequence(int_to_string(sq), s@),
        result >= 0 ==> exists|sq: int| #![auto] generate_squares().contains(sq) && is_subsequence(int_to_string(sq), s@) && result == s.len() as i32 - int_to_string(sq).len() as i32,
        result >= 0 ==> forall|sq: int| #[trigger] generate_squares().contains(sq) && is_subsequence(int_to_string(sq), s@) ==> s.len() as i32 - int_to_string(sq).len() as i32 >= result,
// </vc-spec>
// <vc-code>
{
    assume(false);
    -1
}
// </vc-code>


}

fn main() {}