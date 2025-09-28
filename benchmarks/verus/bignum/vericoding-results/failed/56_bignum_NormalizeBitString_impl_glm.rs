// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn str2int(s: Seq<char>) -> nat
  recommends valid_bit_string(s)
  decreases s.len()
{
  if s.len() == 0 {
    0nat
  } else {
    2nat * str2int(s.subrange(0, s.len() as int - 1)) + 
    (if s[s.len() as int - 1] == '1' { 1nat } else { 0nat })
  }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_adding_leading_zero_preserves_value(s: Seq<char>)
    requires valid_bit_string(s)
    ensures str2int(seq!['0'] + s) == str2int(s)
    decreases s.len()
{
    if s.len() == 0 {
        assert(str2int(seq!['0']) == 0);
        assert(str2int(s) == 0);
    } else {
        let s_init = s.subrange(0, s.len() as int - 1);
        let last = s[s.len() as int - 1];
        lemma_adding_leading_zero_preserves_value(s_init);
        assert(str2int(seq!['0'] + s) == 2 * str2int(seq!['0'] + s_init) + (if last=='1' { 1 } else { 0 }));
        assert(str2int(seq!['0'] + s_init) == str2int(s_init));
        assert(str2int(s) == 2 * str2int(s_init) + (if last=='1' { 1 } else { 0 }));
    }
}

/* helper modified by LLM (iteration 3): combined requires clauses into one */
proof fn lemma_remove_k_leading_zeros(s: Seq<char>, k: nat)
    requires
        valid_bit_string(s),
        k <= s.len(),
        forall|i: int| 0<=i<k ==> s[i]=='0'
    ensures str2int(s) == str2int(s.subrange(k, s.len() as int))
    decreases k
{
    if k == 0 {
    } else {
        let s_rest = s.subrange(1, s.len() as int);
        lemma_adding_leading_zero_preserves_value(s_rest);
        lemma_remove_k_leading_zeros(s_rest, k - 1);
    }
}

/* helper modified by LLM (iteration 3): combined requires clauses into one */
proof fn lemma_all_zeros_value(s: Seq<char>)
    requires
        valid_bit_string(s),
        forall|i: int| 0<=i<s.len() ==> s[i]=='0'
    ensures str2int(s) == 0
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        let s_init = s.subrange(0, s.len() as int - 1);
        lemma_all_zeros_value(s_init);
        assert(str2int(s) == 2 * str2int(s_init) + 0);
    }
}
// </vc-helpers>

// <vc-spec>
fn normalize_bit_string(s: Vec<char>) -> (t: Vec<char>)
  ensures 
    valid_bit_string(t@) &&
    t@.len() > 0 &&
    (t@.len() > 1 ==> t@[0] != '0') &&
    (valid_bit_string(s@) ==> str2int(s@) == str2int(t@))
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fixed while loop invariant syntax */
    let mut cleaned: Vec<char> = Vec::new();
    for c in s {
        if c == '1' {
            cleaned.push('1');
        } else {
            cleaned.push('0');
        }
    }

    let mut start_index = 0;
    let n = cleaned.len();
    while start_index < n && cleaned[start_index] == '0'
        invariant
            0 <= start_index <= n,
            forall|i: int| 0<=i<start_index ==> cleaned[i] == '0',
        decreases n - start_index
    {
        start_index += 1;
    }

    if start_index == n {
        let result = vec!['0'];
        if valid_bit_string(s@) {
            proof {
                lemma_all_zeros_value(cleaned@);
                assert(str2int(seq!['0']) == 0);
            }
        }
        result
    } else {
        let result = cleaned[start_index..].to_vec();
        if valid_bit_string(s@) {
            proof {
                lemma_remove_k_leading_zeros(cleaned@, start_index as nat);
            }
        }
        result
    }
}
// </vc-code>


}

fn main() {}