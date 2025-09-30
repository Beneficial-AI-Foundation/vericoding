// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_binary_string(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
}

spec fn count_zeros(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else if s[0] == '0' {
        1 + count_zeros(s.subrange(1, s.len() as int))
    } else {
        count_zeros(s.subrange(1, s.len() as int))
    }
}

spec fn count_ones(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else if s[0] == '1' {
        1 + count_ones(s.subrange(1, s.len() as int))
    } else {
        count_ones(s.subrange(1, s.len() as int))
    }
}

spec fn longest_non_decreasing_subseq_length_complete(s: Seq<char>) -> int {
    if s.len() == 0 {
        0
    } else if s.len() == 1 {
        1
    } else {
        let count_ones = count_ones(s);
        let count_zeros = s.len() - count_ones;
        if count_zeros == 0 {
            count_ones
        } else if count_ones == 0 {
            1
        } else {
            count_zeros + count_ones
        }
    }
}

spec fn longest_non_decreasing_subseq_length(s: Seq<char>, l: int, r: int) -> int
    recommends 0 <= l <= r < s.len()
{
    let sub = s.subrange(l, r + 1);
    longest_non_decreasing_subseq_length_complete(sub)
}

spec fn basic_valid_solution(s: Seq<char>, t: Seq<char>) -> bool {
    &&& s.len() == t.len()
    &&& valid_binary_string(s)
    &&& valid_binary_string(t)
    &&& (forall|i: int| 0 <= i < s.len() ==> s[i] == '0' ==> t[i] == '0')
    &&& (forall|i: int| 0 <= i < s.len() ==> t[i] == '1' ==> s[i] == '1')
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_basic_solution_identity(s: Seq<char>)
    requires
        valid_binary_string(s),
    ensures
        basic_valid_solution(s, s),
{
}

// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: Vec<char>)
    requires valid_binary_string(s@)
    ensures basic_valid_solution(s@, result@)
// </vc-spec>
// <vc-code>
{
    s
}
// </vc-code>


}

fn main() {}