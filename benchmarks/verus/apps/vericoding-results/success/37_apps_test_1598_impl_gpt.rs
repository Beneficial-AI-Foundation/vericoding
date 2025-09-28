// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_binary_string(s: Seq<char>) -> bool {
    forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

spec fn longest_non_decreasing_subseq(str: Seq<char>) -> nat {
    if str.len() == 0 {
        0
    } else if str.len() == 1 {
        1
    } else {
        longest_non_decreasing_subseq_helper(str, 1, 1, 1)
    }
}

spec fn longest_non_decreasing_subseq_helper(str: Seq<char>, i: int, current_len: nat, max_len: nat) -> nat
    decreases str.len() - i
{
    if i >= str.len() {
        max_len
    } else {
        let new_current_len = if str[i] >= str[i-1] { current_len + 1 } else { 1 };
        let new_max_len = if new_current_len > max_len { new_current_len } else { max_len };
        longest_non_decreasing_subseq_helper(str, i + 1, new_current_len, new_max_len)
    }
}

spec fn count_zeros(str: Seq<char>) -> nat
    decreases str.len()
{
    if str.len() == 0 {
        0
    } else if str[0] == '0' {
        1 + count_zeros(str.subrange(1, str.len() as int))
    } else {
        count_zeros(str.subrange(1, str.len() as int))
    }
}

spec fn same_subsequence_lengths(s: Seq<char>, t: Seq<char>) -> bool {
    forall|l: int, r: int| 0 <= l <= r <= s.len() ==> 
        longest_non_decreasing_subseq(s.subrange(l, r)) == longest_non_decreasing_subseq(t.subrange(l, r))
}

spec fn valid_solution(s: Seq<char>, t: Seq<char>) -> bool {
    s.len() == t.len() && same_subsequence_lengths(s, t)
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_same_subsequence_lengths_refl(s: Seq<char>)
    ensures
        same_subsequence_lengths(s, s),
{
    assert(forall|l: int, r: int| 0 <= l <= r <= s.len() ==>
        longest_non_decreasing_subseq(s.subrange(l, r)) == longest_non_decreasing_subseq(s.subrange(l, r))) by {
    };
}

proof fn lemma_valid_solution_same_seq(s: Seq<char>)
    ensures
        valid_solution(s, s),
{
    lemma_same_subsequence_lengths_refl(s);
}
// </vc-helpers>

// <vc-spec>
fn solve(s: Vec<char>) -> (result: Vec<char>)
    requires
        valid_binary_string(s@),
    ensures
        valid_solution(s@, result@),
// </vc-spec>
// <vc-code>
{
    let ghost s_seq = s@;
    proof { lemma_valid_solution_same_seq(s_seq); }
    let result = s;
    result
}
// </vc-code>


}

fn main() {}