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
/* helper modified by LLM (iteration 5): [Handled base case in recursive proof] */
#[verifier::spinoff_prover]
proof fn count_zeros_append(s: Seq<char>, c: char)
    ensures count_zeros(s.push(c)) == count_zeros(s) + if c == '0' { 1int } else { 0int },
    decreases s.len(),
{
    if s.len() == 0 {
        // Base case
    } else {
        // Recursive step
        count_zeros_append(s.subrange(1, s.len() as int), c);
    }
}

/* helper modified by LLM (iteration 3): [Replaced ext_equal with == for Seq equality] */
proof fn create_zero_seq_push(n: nat)
    ensures create_zero_seq(n).push('0') == create_zero_seq(n+1),
{
    assert(create_zero_seq(n).push('0') == create_zero_seq(n+1));
}

/* helper modified by LLM (iteration 2): [Removed circular reasoning from proof body] */
proof fn forall_char_in_create_zero_seq(n: nat)
    ensures forall|i: int| 0 <= i < n ==> create_zero_seq(n)[i] == '0',
{
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
/* code modified by LLM (iteration 5): [Added invariants and assertions to fix proofs] */
{
    if n == 1 && s[0] == '0' {
        proof {
            assert(s@ == seq!['0']);
            let result_seq = seq!['0'];
            assert(valid_binary_string(result_seq));
            assert(is_minimal_form(s@, result_seq));
        }
        return vec!['0'];
    }

    proof { assert(s@ != seq!['0']); }

    let mut zero_count: usize = 0;
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            valid_binary_string(s@),
            s.len() == n as usize,
            zero_count <= i,
            zero_count as int == count_zeros(s@.subrange(0, i as int)),
        decreases s.len() - i,
    {
        let c = s[i];
        proof {
            let prefix = s@.subrange(0, i as int);
            count_zeros_append(prefix, c);
            assert(prefix.push(c) == s@.subrange(0, (i + 1) as int));
        }
        if c == '0' {
            zero_count = zero_count + 1;
        }
        i = i + 1;
    }

    assert(zero_count as int == count_zeros(s@));

    let mut result = Vec::new();
    result.push('1');

    let mut j: usize = 0;
    while j < zero_count
        invariant
            j <= zero_count,
            count_zeros(s@) == zero_count as int,
            s@ != seq!['0'],
            result@ == seq!['1'] + create_zero_seq(j as nat),
        decreases zero_count - j,
    {
        proof { create_zero_seq_push(j as nat); }
        result.push('0');
        j = j + 1;
    }

    proof {
        let res_seq = result@;
        let num_zeros = count_zeros(s@) as nat;
        assert(res_seq == seq!['1'] + create_zero_seq(num_zeros));
        assert(is_minimal_form(s@, res_seq));

        assert(res_seq.len() > 0);
        assert(res_seq[0] == '1');
        let s_zeros = create_zero_seq(num_zeros);
        forall_char_in_create_zero_seq(num_zeros);
        assert forall|k: int| 0 <= k < res_seq.len() implies res_seq[k] == '0' || res_seq[k] == '1' by {
            if k == 0 {
                assert(res_seq[k] == '1');
            } else {
                assert(res_seq[k] == s_zeros[k as int - 1]);
                assert(s_zeros[k as int - 1] == '0');
            }
        }
        assert(valid_binary_string(res_seq));
    }

    result
}

// </vc-code>


}

fn main() {}