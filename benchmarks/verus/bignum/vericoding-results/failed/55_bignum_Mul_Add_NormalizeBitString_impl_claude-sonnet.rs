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
/* helper modified by LLM (iteration 10): use ghost to access spec-only types safely */
fn seq_to_vec(s: Seq<char>) -> (v: Vec<char>)
    ensures v@ == s
{
    let mut v = Vec::new();
    let mut i: usize = 0;
    while i < s.len() as usize
        invariant
            i <= s.len(),
            v@.len() == i,
            forall|j: int| 0 <= j < i ==> v@[j] == s[j],
        decreases s.len() - i
    {
        proof {
            let ghost_index: int = i as int;
            assert(0 <= ghost_index < s.len());
        }
        v.push(s[i as usize]);
        i += 1;
    }
    v
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
    /* code modified by LLM (iteration 10): keep multiplication logic unchanged from previous iteration */
    if s1.len() == 0 || s2.len() == 0 {
        return vec!['0'];
    }
    
    let mut result = vec!['0'];
    
    let mut i: usize = 0;
    while i < s1.len()
        invariant
            i <= s1.len(),
            valid_bit_string(result@),
        decreases s1.len() - i
    {
        if s1[s1.len() - 1 - i] == '1' {
            let mut shifted_s2 = vec!['0'; i];
            shifted_s2.append(&mut s2.clone());
            let add_result = add(result@, shifted_s2@);
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