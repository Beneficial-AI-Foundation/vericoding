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
proof fn lemma_str2int_zero_append(s: Seq<char>) 
    requires ValidBitString(s), s.len() > 0, s.index(s.len() as int - 1) == '0'
    ensures Str2Int(s) == 2 * Str2Int(s.subrange(0, s.len() as int - 1)),
proof fn lemma_str2int_one_append(s: Seq<char>) 
    requires ValidBitString(s), s.len() > 0, s.index(s.len() as int - 1) == '1'
    ensures Str2Int(s) == 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + 1,
proof fn lemma_str2int_double_and_add_half(s: Seq<char>) 
    requires ValidBitString(s), s.len() > 0
    ensures 2 * Str2Int(s) == Str2Int(s + seq!['0']) || 2 * Str2Int(s) + 1 == Str2Int(s + seq!['1'])
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2_Mul(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let n = b.len();
    let mut power: Vec<char> = a.to_vec();
    
    for i in 0..n {
        if b[i] == '1' {
            let mut temp = result.clone();
            while temp.len() < power.len() {
                temp.push('0');
            }
            while power.len() < temp.len() {
                power.push('0');
            }
            result = Vec::new();
            let mut carry = '0';
            for j in 0..temp.len() {
                let (sum, new_carry) = add_bits(temp[j], power[j], carry);
                result.push(sum);
                carry = new_carry;
            }
            if carry == '1' {
                result.push('1');
            }
        }
        
        // Square the power
        let mut new_power = Vec::new();
        let mut carry = '0';
        for j in 0..power.len() {
            let (product, new_carry) = mul_bits(power[j], power[j], carry);
            new_power.push(product);
            carry = new_carry;
        }
        if carry == '1' {
            new_power.push('1');
        }
        power = new_power;
    }
    
    result
}
// </vc-code>

fn main() {}
}

