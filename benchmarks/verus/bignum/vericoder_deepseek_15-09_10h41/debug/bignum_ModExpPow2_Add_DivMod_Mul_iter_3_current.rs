
use vstd::prelude::*;

verus! {

spec fn Str2Int(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  if s.len() == 0 {
    0
  } else {
    2 * Str2Int(s.subrange(0, s.len() as int - 1))
      + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat })
  }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
/* helper modified by LLM (iteration 3): Added executable helper functions with proper signatures */
fn append_bit_strings(s1: &[char], s2: &[char]) -> Vec<char> 
    requires 
        ValidBitString(s1@), 
        ValidBitString(s2@),
    ensures 
        ValidBitString(result@)
{
    let mut result = Vec::new();
    result.extend_from_slice(s1);
    result.extend_from_slice(s2);
    result
}

fn multiply_by_two(s: &[char]) -> Vec<char> 
    requires 
        ValidBitString(s@),
    ensures 
        ValidBitString(result@)
{
    let mut result = Vec::new();
    result.extend_from_slice(s);
    result.push('0');
    result
}
// </vc-helpers>

// <vc-spec>
exec fn ModExpPow2_Add_DivMod_Mul(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Use executable helper functions instead of proof/spec functions */
{
    let mut result = Vec::new();
    let mut power_seq = a.to_owned();

    for i in 0..b.len()
        invariant
            ValidBitString(result@),
            ValidBitString(power_seq@),
        decreases b.len() - i
    {
        if b[i] == '1' {
            result = append_bit_strings(&result, &power_seq);
        }
        
        if i < b.len() - 1 {
            power_seq = multiply_by_two(&power_seq);
        }
    }
    
    result
}
// </vc-code>

fn main() {}
}

