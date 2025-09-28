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
/* helper modified by LLM (iteration 4): No changes needed. */
proof fn lemma_int_to_string_pos(n: int)
    requires n >= 0
    ensures n > 0 ==> int_to_string_helper(n) == int_to_string(n)
{
    if n == 0 { /* no specific proof needed for n=0 */ }
    else if n < 10 {
        assert(int_to_string_helper(n) =~= seq![('0' as u8 + (n % 10) as u8) as char]);
    } else {
        lemma_int_to_string_pos(n / 10);
        assert(int_to_string_helper(n / 10).add(seq![('0' as u8 + (n % 10) as u8) as char]) =~= int_to_string(n));
    }
}

proof fn lemma_int_to_string_len(n: int)
    requires n >= 0
    ensures int_to_string(n).len() == int_to_string_len_spec(n)
{
    if n == 0 {
    } else if n < 10 {
    } else {
        lemma_int_to_string_len(n / 10);
    }
}

spec fn int_to_string_len_spec(n: int) -> nat
    decreases n when n >= 0
{
    if n == 0 { 1 }
    else if n < 10 { 1 }
    else { (1 + int_to_string_len_spec(n / 10)) as nat }
}
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
/* code modified by LLM (iteration 4): Cast `s_seq.len()` and `sq_str.len()` to `i32` within the `current_removal` calculation to avoid Verus type errors. */
{
    let s_seq = s@;
    let squares = generate_squares();
    let mut min_removal: i32 = -1;

    let mut i: int = 0;
    while i < squares.len()
        invariant
            0 <= i <= squares.len(),
            min_removal == -1 || (
                min_removal >= 0
                && forall|j: int| 0 <= j < i && #[trigger] squares.contains(squares@[j]) && is_subsequence(int_to_string(squares@[j]), s_seq)
                    ==> (s_seq.len() as int - int_to_string(squares@[j]).len() as int) >= min_removal as int
            ),
    {
        let sq = squares@[i];
        let sq_str = int_to_string(sq);

        if is_subsequence(sq_str, s_seq) {
            let current_removal: i32 = s_seq.len() as i32 - sq_str.len() as i32;
            if min_removal == -1 || current_removal < min_removal {
                min_removal = current_removal;
            }
        }
        i = i + 1;
    }
    min_removal
}
// </vc-code>


}

fn main() {}