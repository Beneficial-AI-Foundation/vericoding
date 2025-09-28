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
/* helper modified by LLM (iteration 5): prove generate_squares_helper contains any square in range */
proof fn generate_squares_helper_contains(start: int, end: int, i: int)
    requires
        start <= i && i <= end,
    ensures
        generate_squares_helper(start,end).contains(i * i),
    decreases
        end + 1 - start
{
    if start > end {
        // impossible case for the requires
    } else if start == i {
        // head of the sequence is start*start
        assert(generate_squares_helper(start, end).contains(start * start));
    } else {
        // start < i: the element must be contained in the tail
        generate_squares_helper_contains(start + 1, end, i);
        assert(generate_squares_helper(start, end).contains(i * i));
    }
}

/* helper modified by LLM (iteration 5): prove generate_squares contains i*i for 1..44721 */
proof fn generate_squares_contains(i: int)
    requires
        1 <= i && i <= 44721,
    ensures
        generate_squares().contains(i * i),
    decreases
        44722 - i
{
    // generate_squares == generate_squares_helper(1, 44721)
    generate_squares_helper_contains(1, 44721, i);
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
{
    /* code modified by LLM (iteration 5): perform search in a proof block over spec squares and produce runtime result */
    let mut result: i32 = -1;
    proof {
        let squares = generate_squares();
        let mut i: int = 0;
        let mut found: bool = false;
        let mut best: int = 0;
        let total_len: int = s.len() as int;

        while i < 44721
            invariant
                0 <= i && i <= 44721,
            decreases
                44721 - i
        {
            let sq = squares@[i];
            let str_sq = int_to_string(sq);
            if is_subsequence(str_sq, s@) {
                let cand = total_len - str_sq.len();
                if !found {
                    found = true;
                    best = cand;
                } else if cand < best {
                    best = cand;
                }
            }
            i = i + 1;
        }

        if found {
            result = best as i32;
        } else {
            result = -1;
        }
    }
    result
}
// </vc-code>


}

fn main() {}