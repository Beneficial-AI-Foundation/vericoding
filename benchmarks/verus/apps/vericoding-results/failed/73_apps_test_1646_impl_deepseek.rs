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

proof fn count_zeros_lemma(s: Seq<char>, i: int)
    requires
        0 <= i <= s.len(),
        valid_binary_string(s),
    ensures
        count_zeros(s.subrange(i, s.len())) >= 0,
decreases s.len() - i
{
    if i < s.len() {
        count_zeros_lemma(s, i + 1);
    }
}

proof fn create_zero_seq_lemma(n: nat)
    ensures
        create_zero_seq(n).len() == n,
        forall|i: int| 0 <= i < n ==> create_zero_seq(n)[i] == '0',
{
}

proof fn minimal_form_preserves_validity(s: Seq<char>, result: Seq<char>)
    requires
        valid_binary_string(s),
        is_minimal_form(s, result),
    ensures
        valid_binary_string(result),
{
    if s == seq!['0'] {
        assert(result == seq!['0']);
    } else {
        assert(result == seq!['1'] + create_zero_seq(count_zeros(s) as nat));
        create_zero_seq_lemma(count_zeros(s) as nat);
        count_zeros_lemma(s, 0);
    }
}

proof fn seq_eq_lemma(s1: Seq<char>, s2: Seq<char>)
    ensures
        s1 == s2 <==> (s1.len() == s2.len() && forall|i: int| 0 <= i < s1.len() ==> s1[i] == s2[i]),
{
}

proof fn count_zeros_nonnegative_lemma(s: Seq<char>, i: nat)
    requires
        0 <= i <= s.len(),
        valid_binary_string(s),
    ensures
        count_zeros(s.subrange(i as int, s.len())) >= 0,
{
    count_zeros_lemma(s, i as int);
}

proof fn count_zeros_type_conversion_lemma(zero_count_int: int)
    requires
        zero_count_int >= 0,
    ensures
        zero_count_int >= 0,
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
{
    /* code modified by LLM (iteration 5): fixed type errors in sequence indexing and casting */
    seq_eq_lemma(s@, seq!['0']);
    if s@.len() == 1 as nat && s@[0] == '0' {
        let result: Vec<char> = vec!['0'];
        result
    } else {
        count_zeros_lemma(s@, 0);
        let zero_count_int = count_zeros(s@);
        assert(zero_count_int >= 0);
        count_zeros_type_conversion_lemma(zero_count_int);
        let zero_count: usize = if zero_count_int == 0 { 0 } else { (zero_count_int as nat) as usize };
        let mut result_vec: Vec<char> = Vec::with_capacity(zero_count + 1);
        result_vec.push('1');
        let mut i: usize = 0;
        while i < zero_count
            invariant
                0 <= i <= zero_count,
                result_vec@.len() == i + 1,
                result_vec@[0] == '1',
                forall|j: int| 1 <= j < i + 1 ==> result_vec@[j] == '0',
        {
            result_vec.push('0');
            i += 1;
        }
        let result = result_vec;
        minimal_form_preserves_validity(s@, result@);
        result
    }
}
// </vc-code>


}

fn main() {}