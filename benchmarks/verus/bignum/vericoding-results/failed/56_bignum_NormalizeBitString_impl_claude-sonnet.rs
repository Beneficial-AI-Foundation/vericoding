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
proof fn lemma_str2int_empty_prefix(s: Seq<char>)
    requires valid_bit_string(s), s.len() > 0, s[0] == '0'
    ensures str2int(s) == str2int(s.subrange(1, s.len() as int))
    decreases s.len()
{
    if s.len() == 1 {
        assert(s.subrange(1, 1).len() == 0);
        assert(str2int(s.subrange(1, 1)) == 0);
        assert(str2int(s) == 2 * str2int(s.subrange(0, 0)) + 0);
        assert(str2int(s.subrange(0, 0)) == 0);
    } else {
        let prefix = s.subrange(0, s.len() as int - 1);
        let suffix = s.subrange(1, s.len() as int);
        let suffix_prefix = suffix.subrange(0, suffix.len() as int - 1);
        assert(prefix.subrange(1, prefix.len() as int) =~= suffix_prefix);
        lemma_str2int_empty_prefix(prefix);
    }
}

proof fn lemma_valid_bit_string_subrange(s: Seq<char>, start: int, end: int)
    requires valid_bit_string(s), 0 <= start <= end <= s.len()
    ensures valid_bit_string(s.subrange(start, end))
{
    let sub = s.subrange(start, end);
    assert forall|i: int| 0 <= i < sub.len() implies (sub[i] == '0' || sub[i] == '1') by {
        assert(sub[i] == s[start + i]);
        assert(0 <= start + i < s.len());
    }
}

/* helper modified by LLM (iteration 10): Added executable valid bit string check */
fn check_valid_bit_string(v: &Vec<char>) -> (result: bool)
    ensures result <==> valid_bit_string(v@)
{
    let mut i = 0;
    while i < v.len()
        invariant
            0 <= i <= v.len(),
            forall|j: int| 0 <= j < i ==> (v@[j] == '0' || v@[j] == '1')
        decreases v.len() - i
    {
        if v[i] != '0' && v[i] != '1' {
            return false;
        }
        i += 1;
    }
    true
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
    /* code modified by LLM (iteration 10): Fixed postcondition by ensuring proper invariant maintenance */
    if s.len() == 0 {
        let mut result = Vec::new();
        result.push('0');
        return result;
    }
    
    // First ensure we have a valid bit string
    if !check_valid_bit_string(&s) {
        let mut result = Vec::new();
        result.push('0');
        return result;
    }
    
    // s is now known to be valid
    let mut result = s;
    
    while result.len() > 1 && result[0] == '0'
        invariant
            result@.len() > 0,
            valid_bit_string(result@),
            str2int(s@) == str2int(result@)
        decreases result.len()
    {
        proof {
            lemma_valid_bit_string_subrange(result@, 1, result@.len() as int);
            lemma_str2int_empty_prefix(result@);
        }
        result.remove(0);
    }
    
    result
}
// </vc-code>


}

fn main() {}