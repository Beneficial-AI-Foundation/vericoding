// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_binary_string(s: Seq<char>) -> bool {
    s.len() > 0 && 
    (forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1') &&
    (s == seq!['0'] || s[0] == '1')
}

spec fn count_zeros(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() == 0 { 
        0int
    } else { 
        (if s[0] == '0' { 1int } else { 0int }) + count_zeros(s.subrange(1, s.len() as int))
    }
}

spec fn create_zero_seq(n: nat) -> Seq<char> {
    Seq::new(n, |i: int| '0')
}

spec fn is_minimal_form(s: Seq<char>, result: Seq<char>) -> bool {
    (s == seq!['0'] ==> result == seq!['0'])
    &&
    (s != seq!['0'] ==> result == seq!['1'] + create_zero_seq(count_zeros(s) as nat))
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added `lemma_zero_count_subrange` for proving total zero count. */
proof fn lemma_is_minimal_form_zero_case() 
    ensures 
        is_minimal_form(seq!['0'], seq!['0']), 
{
    assert(is_minimal_form(seq!['0'], seq!['0'])) by {
        assert(seq!['0'] == seq!['0']);
    };
}

proof fn lemma_zero_count_subrange(s: Seq<char>, idx: int)
    requires
        0 <= idx && idx <= s.len(),
    ensures
        count_zeros(s.subrange(0, idx)) + count_zeros(s.subrange(idx, s.len())) == count_zeros(s),
    decreases
        (s.len() - idx)
{
    if idx < s.len() {
        lemma_zero_count_subrange(s, idx + 1);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: u8, s: Vec<char>) -> (result: Vec<char>)
    requires 
        n >= 1 && n <= 100,
        s.len() == n as usize,
        valid_binary_string(s@),
    ensures 
        valid_binary_string(result@),
        is_minimal_form(s@, result@),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected `lemma_zero_count_subrange` call and updated loop invariant for `zero_count` to avoid an index out of bounds error. */
{
    let s_seq = s@;
    let mut zero_count: int = 0;
    if s_seq.len() == 1 && s_seq[0] == '0' {
        proof {
            lemma_is_minimal_form_zero_case();
        }
        let mut zero_vec = Vec::new();
        zero_vec.push('0');
        return zero_vec;
    }

    let mut i: int = 0;
    while i < s_seq.len()
        invariant
            0 <= i && i <= s_seq.len(),
            zero_count == count_zeros(s_seq.subrange(0, i)),
            s.len() == s_seq.len(),
            s@ == s_seq,
    {
        if s_seq[i] == '0' {
            zero_count = zero_count + 1;
        }
        i = i + 1;
    }

    let mut result_vec = Vec::new();
    result_vec.push('1');

    proof {
        lemma_zero_count_subrange(s_seq, s_seq.len() as int);
        assert(zero_count == count_zeros(s_seq.subrange(0, s_seq.len())));
        assert(count_zeros(s_seq.subrange(0, s_seq.len())) == count_zeros(s_seq));
    }

    let mut j: int = 0;
    while j < zero_count
        invariant
            0 <= j && j <= zero_count,
            result_vec@ == (seq!['1'] + create_zero_seq(j as nat)),
            s.len() == s_seq.len(),
            s@ == s_seq,
            zero_count == count_zeros(s_seq),
    {
        result_vec.push('0');
        j = j + 1;
    }
    
    proof {
        assert(is_minimal_form(s_seq, result_vec@)) by {
            assert(s_seq != seq!['0']); // From the initial if statement
            assert(result_vec@ == seq!['1'] + create_zero_seq(count_zeros(s_seq) as nat));
        }
    }
    result_vec
}
// </vc-code>


}

fn main() {}