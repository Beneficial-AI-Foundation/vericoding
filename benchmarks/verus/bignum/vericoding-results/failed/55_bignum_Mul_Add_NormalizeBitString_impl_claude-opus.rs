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
/* helper modified by LLM (iteration 10): Fixed indexing to use usize directly without casting to int */
spec fn pow2(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { 2 * pow2((n - 1) as nat) }
}

fn add_vec(s1: Vec<char>, s2: Vec<char>) -> (res: Vec<char>)
    requires
        valid_bit_string(s1@) && valid_bit_string(s2@),
    ensures
        valid_bit_string(res@) &&
        str2int(res@) == str2int(s1@) + str2int(s2@),
{
    let seq_result = add(s1@, s2@);
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < seq_result.len()
        invariant
            0 <= i <= seq_result.len(),
            result@.len() == i as nat,
            forall|j: int| 0 <= j < i as int ==> result@[j] == seq_result[j],
    {
        proof {
            assert(seq_result[i as int] == '0' || seq_result[i as int] == '1');
        }
        let c = seq_result[i as int];
        result.push(c);
        i = i + 1;
    }
    result
}

fn normalize_vec(s: Vec<char>) -> (res: Vec<char>)
    ensures
        valid_bit_string(res@) &&
        res@.len() > 0 &&
        (res@.len() > 1 ==> res@[0] != '0') &&
        (valid_bit_string(s@) ==> str2int(s@) == str2int(res@)),
{
    let seq_result = normalize_bit_string(s@);
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < seq_result.len()
        invariant
            0 <= i <= seq_result.len(),
            result@.len() == i as nat,
            forall|j: int| 0 <= j < i as int ==> result@[j] == seq_result[j],
    {
        proof {
            assert(seq_result[i as int] == '0' || seq_result[i as int] == '1');
        }
        let c = seq_result[i as int];
        result.push(c);
        i = i + 1;
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
/* code modified by LLM (iteration 10): Keep original implementation */
{
    let mut result = vec!['0'];
    let n1 = s1.len();
    let n2 = s2.len();
    
    let mut i: usize = 0;
    while i < n2
        invariant
            0 <= i <= n2,
            valid_bit_string(result@),
            valid_bit_string(s1@),
            valid_bit_string(s2@),
            str2int(result@) == str2int(s1@) * str2int(s2@.subrange(0, i as int)),
    {
        if s2[n2 - 1 - i] == '1' {
            let mut shifted = s1.clone();
            let mut j: usize = 0;
            while j < i
                invariant
                    0 <= j <= i,
                    valid_bit_string(shifted@),
                    str2int(shifted@) == str2int(s1@) * pow2(j as nat),
            {
                shifted.push('0');
                j = j + 1;
            }
            result = add_vec(result, shifted);
        }
        i = i + 1;
    }
    
    normalize_vec(result)
}
// </vc-code>


}

fn main() {}