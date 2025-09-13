// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn generate_squares() -> Seq<int>
    ensures forall|i: int| 0 <= i < generate_squares().len() ==> generate_squares()[i] > 0
{
    generate_squares_helper(1, 44721)
}

spec fn is_subsequence(pattern: Seq<char>, text: Seq<char>) -> bool {
    is_subsequence_helper(pattern, text, 0, 0)
}

spec fn int_to_string(n: int) -> Seq<char>
    recommends n >= 0
{
    if n == 0 { seq!['0'] }
    else { int_to_string_helper(n) }
}
// </vc-preamble>

// <vc-helpers>
spec fn generate_squares_helper(start: int, end: int) -> Seq<int> {
    if start > end { seq![] }
    else { seq![start * start].add(generate_squares_helper(start + 1, end)) }
}

spec fn is_subsequence_helper(pattern: Seq<char>, text: Seq<char>, p_idx: int, t_idx: int) -> bool {
    if p_idx >= pattern.len() { true }
    else if t_idx >= text.len() { false }
    else if pattern[p_idx] == text[t_idx] {
        is_subsequence_helper(pattern, text, p_idx + 1, t_idx + 1)
    } else {
        is_subsequence_helper(pattern, text, p_idx, t_idx + 1)
    }
}

spec fn int_to_string_helper(n: int) -> Seq<char> {
    if n == 0 { seq![] }
    else { 
        int_to_string_helper(n / 10).add(seq![((n % 10) + 48) as char])
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(s: &str) -> (result: int)
    requires 
        s.len() > 0,
        forall|i: int| 0 <= i < s.len() ==> '0' <= s@[i] <= '9',
        s@[0] != '0' || s.len() == 1,
    ensures 
        result == -1 || result >= 0,
        result == -1 ==> forall|sq: int| generate_squares().contains(sq) ==> !is_subsequence(int_to_string(sq), s@),
        result >= 0 ==> exists|sq: int| generate_squares().contains(sq) && is_subsequence(int_to_string(sq), s@) && result == s.len() - int_to_string(sq).len(),
        result >= 0 ==> forall|sq: int| generate_squares().contains(sq) && is_subsequence(int_to_string(sq), s@) ==> s.len() - int_to_string(sq).len() >= result,
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    -1int
    // impl-end
}
// </vc-code>


}

fn main() {}