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
/* helper modified by LLM (iteration 2): fixed type issues and simplified helpers */
proof fn lemma_str2int_empty()
    ensures Str2Int(Seq::<char>::empty()) == 0
{
}

proof fn lemma_str2int_append_zero(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s.push('0')) == 2 * Str2Int(s)
{
}

proof fn lemma_str2int_append_one(s: Seq<char>)
    requires ValidBitString(s)
    ensures Str2Int(s.push('1')) == 2 * Str2Int(s) + 1
{
}

proof fn lemma_str2int_distributive(s1: Seq<char>, s2: Seq<char>)
    requires ValidBitString(s1), ValidBitString(s2)
    ensures Str2Int(s1) * Str2Int(s2) == Str2Int(s2) * Str2Int(s1)
{
}

exec fn add_bit_strings(s1: &[char], s2: &[char]) -> (res: Vec<char>)
    requires ValidBitString(s1@), ValidBitString(s2@)
    ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
{
    let mut result = Vec::new();
    let mut carry = false;
    let mut i = 0;
    
    while i < s1.len().max(s2.len())
        invariant ValidBitString(result@)
    {
        let bit1 = if i < s1.len() { s1[i] == '1' } else { false };
        let bit2 = if i < s2.len() { s2[i] == '1' } else { false };
        
        let sum = bit1 as u8 + bit2 as u8 + carry as u8;
        if sum >= 2 {
            result.push('1');
            carry = true;
        } else if sum == 1 {
            result.push('1');
            carry = false;
        } else {
            result.push('0');
            carry = false;
        }
        i += 1;
    }
    
    if carry {
        result.push('1');
    }
    
    result
}
// </vc-helpers>

// <vc-spec>
exec fn Mul_NormalizeBitString(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed type comparison by using int instead of nat */
    if s1.len() == 0 || s2.len() == 0 {
        return Vec::new();
    }
    
    let mut result = Vec::new();
    let mut i: int = 0;
    let s2_int_val = Str2Int(s2@) as int;
    
    while i < s2_int_val
        invariant ValidBitString(result@)
    {
        result = add_bit_strings(&result, s1);
        i += 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}
