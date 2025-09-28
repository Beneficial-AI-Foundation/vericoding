// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() == 0 { 0nat } else { 2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
}

fn add(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2),
  ensures 
    valid_bit_string(res) &&
    str2int(res) == str2int(s1) + str2int(s2),
{
  assume(false);
  unreached()
}

fn normalize_bit_string(s: Seq<char>) -> (t: Seq<char>)
  ensures 
    valid_bit_string(t) &&
    t.len() > 0 &&
    (t.len() > 1 ==> t[0] != '0') &&
    (valid_bit_string(s) ==> str2int(s) == str2int(t)),
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): fixed casting issue by using proper bounds checking */
proof fn get_seq_char(s: Seq<char>, i: int) -> (c: char)
    requires 0 <= i < s.len()
    ensures c == s[i]
{
    s[i]
}

fn seq_to_vec(s: Seq<char>) -> (res: Vec<char>)
    requires valid_bit_string(s)
    ensures res@ == s && valid_bit_string(res@)
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result.len() == i,
            result@ == s.subrange(0, i as int),
            valid_bit_string(result@)
        decreases s.len() - i
    {
        let ghost_char = proof { get_seq_char(s, i as int) };
        result.push(ghost_char);
        i += 1;
    }
    result
}
// </vc-helpers>

// <vc-spec>
fn mul(s1: Vec<char>, s2: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(s1@) && valid_bit_string(s2@),
  ensures 
    valid_bit_string(res@) &&
    str2int(res@) == str2int(s1@) * str2int(s2@),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): removed casting to fix compilation error */
    let mut result = vec!['0'];
    let mut i: usize = 0;
    while i < s2.len()
        invariant
            0 <= i <= s2.len(),
            valid_bit_string(result@),
            str2int(result@) == str2int(s1@) * str2int(s2@.subrange(0, i as int))
        decreases s2.len() - i
    {
        let ghost bit = proof { get_seq_char(s2@, (s2.len() - 1 - i) as int) };
        if bit == '1' {
            let shifted_s1 = {
                let mut shifted = vec!['0'; s1.len() + i];
                let mut j: usize = 0;
                while j < s1.len()
                    invariant
                        0 <= j <= s1.len(),
                        shifted.len() == s1.len() + i,
                        forall|k: int| 0 <= k < j ==> shifted@[k] == s1@[k],
                        forall|k: int| j <= k < shifted.len() ==> shifted@[k] == '0',
                        valid_bit_string(shifted@)
                    decreases s1.len() - j
                {
                    let ghost char_val = proof { get_seq_char(s1@, j as int) };
                    shifted.set(j, char_val);
                    j += 1;
                }
                shifted
            };
            let add_result = add(result@, shifted_s1@);
            result = seq_to_vec(add_result);
        }
        i += 1;
    }
    let normalized = normalize_bit_string(result@);
    seq_to_vec(normalized)
}
// </vc-code>


}

fn main() {}