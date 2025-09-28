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
/* helper modified by LLM (iteration 5): remove proof block from non-decreases spec function */
proof fn lemma_subseq_len_preserves_structure(s: Seq<char>, t: Seq<char>)
    requires
        s.len() == t.len(),
        valid_binary_string(s),
        valid_binary_string(t),
        s == t,
    ensures
        same_subsequence_lengths(s, t),
{
    // For identical sequences, subsequence lengths are trivially equal
}

proof fn lemma_copy_preserves_validity(s: Seq<char>)
    requires
        valid_binary_string(s),
    ensures
        valid_binary_string(s),
{
}

proof fn lemma_same_seq_same_subseq(s: Seq<char>)
    requires
        valid_binary_string(s),
    ensures
        same_subsequence_lengths(s, s),
{
    assert(forall|l: int, r: int| 0 <= l <= r <= s.len() ==> 
        longest_non_decreasing_subseq(s.subrange(l, r)) == longest_non_decreasing_subseq(s.subrange(l, r)));
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
    /* code modified by LLM (iteration 5): simplified to just copy the sequence and call the right lemma */
    let mut result = Vec::new();
    
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result.len() == i,
            valid_binary_string(s@),
            valid_binary_string(result@),
            forall|j: int| 0 <= j < i ==> result@[j] == s@[j],
        decreases s.len() - i
    {
        result.push(s[i]);
        i += 1;
    }
    
    proof {
        assert(result@ == s@);
        lemma_same_seq_same_subseq(s@);
    }
    
    result
}
// </vc-code>


}

fn main() {}