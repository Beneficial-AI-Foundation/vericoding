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
/* helper modified by LLM (iteration 5): Fix type compatibility by using int instead of nat in count_odd_even */
spec fn count_odd_even(s: Seq<char>) -> (int, int)
    decreases s.len()
{
    if s.len() == 0 {
        (0, 0)
    } else if s.len() == 1 {
        (0, 1)
    } else {
        let (prev_even, prev_odd) = count_odd_even(s.subrange(1, s.len() as int));
        if s[0] == s[1] {
            (prev_even, prev_odd)
        } else {
            (prev_even + 1, prev_odd)
        }
    }
}

proof fn lemma_count_odd_even_valid(s: Seq<char>)
    requires
        valid_input(s),
    ensures
        valid_output(s, count_odd_even(s).0, count_odd_even(s).1),
{
    if s.len() == 0 {
        assert(valid_output(s, 0, 0));
    } else if s.len() == 1 {
        assert(valid_output(s, 0, 1));
    } else {
        lemma_count_odd_even_valid(s.subrange(1, s.len() as int));
        let (prev_even, prev_odd) = count_odd_even(s.subrange(1, s.len() as int));
        if s[0] == s[1] {
            assert(count_odd_even(s) == (prev_even, prev_odd));
            assert(valid_output(s, prev_even, prev_odd));
        } else {
            assert(count_odd_even(s) == (prev_even + 1, prev_odd));
            assert(valid_output(s, prev_even + 1, prev_odd));
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: (u32, u32))
    requires valid_input(s@)
    ensures valid_output(s@, result.0 as int, result.1 as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fix return type conversion using int results and proper u32 casting */
{
    proof {
        lemma_count_odd_even_valid(s@);
    }
    let (even_int, odd_int) = count_odd_even(s@);
    (even_int as u32, odd_int as u32)
}
// </vc-code>


}

fn main() {}