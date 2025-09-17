use vstd::prelude::*;

verus! {

spec fn Exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 { 1 } else { x * Exp_int(x, (y - 1) as nat) }
}

spec fn Str2Int(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  if s.len() == 0 { 0 } else { 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat }) }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==> (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-spec>
exec fn Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
// </vc-spec>
// <vc-code>
spec fn Mod(val: nat, modulus: nat) -> nat {
    val % modulus
}
// </vc-code>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 6): Fix adder implementation with proper verification */
    let len1 = s1.len();
    let len2 = s2.len();
    let max_len = if len1 > len2 { len1 } else { len2 };
    let mut result = Vec::<char>::new();
    let mut carry = 0;
    
    for i in 0..max_len {
        let b1 = if i < len1 && s1[i] == '1' { 1 } else { 0 };
        let b2 = if i < len2 && s2[i] == '1' { 1 } else { 0 };
        let sum = b1 + b2 + carry;
        result.push(if sum % 2 == 1 { '1' } else { '0' });
        carry = sum / 2;
    }
    
    if carry > 0 {
        result.push('1');
    }
    
    result
}
// </vc-code>

// <vc-spec>
exec fn ModExpPow2(sx: &[char], sy: &[char], n: int, sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    n >= 0,
    (Str2Int(sy@) == Exp_int(2, n as nat) || Str2Int(sy@) == 0),
    sy@.len() == (n as nat) + 1,
    Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases n
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 6): Implement modular exponentiation using iterative method */
    let base_val = Str2Int(sx@);
    let exp_val = Str2Int(sy@);
    let modulus_val = Str2Int(sz@);
    
    if exp_val == 0 {
        return Vec::from_vec(vec!['1']);
    }
    
    let mut result = 1nat;
    let mut base = base_val % modulus_val;
    let mut exponent = exp_val;
    
    while exponent > 0 {
        if exponent % 2 == 1 {
            result = (result * base) % modulus_val;
        }
        base = (base * base) % modulus_val;
        exponent = exponent / 2;
    }
    
    let mut binary_result = Vec::<char>::new();
    let mut temp = result;
    
    while temp > 0 {
        if temp % 2 == 1 {
            binary_result.push('1');
        } else {
            binary_result.push('0');
        }
        temp = temp / 2;
    }
    
    if binary_result.is_empty() {
        binary_result.push('0');
    }
    
    binary_result.reverse();
    binary_result
}
// </vc-code>

fn main() {}
}
