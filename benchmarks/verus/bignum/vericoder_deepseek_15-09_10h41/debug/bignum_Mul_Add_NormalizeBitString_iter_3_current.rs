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
/* helper modified by LLM (iteration 3): improved binary_multiplication with proper implementation */
fn binary_multiplication(s1: &[char], s2: &[char]) -> Vec<char>
    requires ValidBitString(s1@), ValidBitString(s2@)
    ensures ValidBitString(result@), Str2Int(result@) == Str2Int(s1@) * Str2Int(s2@)
{
    let len1 = s1.len();
    let len2 = s2.len();
    let mut result = Vec::with_capacity(len1 + len2);
    
    for i in 0..len1 + len2 {
        result.push('0');
    }
    
    for i in (0..len2).rev() {
        if s2[i] == '1' {
            let mut carry = '0';
            for j in (0..len1).rev() {
                let index = i + j + 1;
                let bit1 = if result[index] == '1' { 1 } else { 0 };
                let bit2 = if s1[j] == '1' { 1 } else { 0 };
                let sum = bit1 + bit2 + (if carry == '1' { 1 } else { 0 });
                
                result[index] = if sum % 2 == 1 { '1' } else { '0' };
                carry = if sum >= 2 { '1' } else { '0' };
            }
            result[i] = if carry == '1' { '1' } else { '0' };
        }
    }
    
    result
}
// </vc-helpers>

// <vc-spec>
exec fn Mul_Add_NormalizeBitString(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): fixed result variable and simplified implementation */
{
    let result = binary_multiplication(s1, s2);
    
    proof {
        assert(ValidBitString(result@));
        assert(Str2Int(result@) == Str2Int(s1@) * Str2Int(s2@));
    }
    
    result
}
// </vc-code>

fn main() {}
}
