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
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Fixed recursive call issue by implementing binary multiplication algorithm */
    if s1.len() == 0 || s2.len() == 0 {
        return vec!['0'];
    }
    
    let mut result = vec!['0'];
    let mut i = 0;
    
    while i < s1.len()
        invariant
            ValidBitString(result@),
            i <= s1.len(),
            ValidBitString(s1@),
            ValidBitString(s2@)
    {
        if s1[i] == '1' {
            let mut carry = 0;
            let mut temp_result = Vec::<char>::new();
            let mut j = 0;
            
            while j < s2.len() || carry > 0
                invariant
                    ValidBitString(temp_result@),
                    j <= s2.len(),
                    carry <= 1
            {
                let bit1 = if j < s2.len() { if s2[j] == '1' { 1 } else { 0 } } else { 0 };
                let sum = bit1 + carry;
                temp_result.push(if sum % 2 == 1 { '1' } else { '0' });
                carry = sum / 2;
                j += 1;
            }
            
            result = temp_result;
        }
        
        i += 1;
    }
    
    if result.len() == 0 {
        result.push('0');
    }
    
    result
}
// </vc-code>

// <vc-spec>
exec fn ModExp(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): Replaced to_vec() with manual copying to avoid unsupported operations */
    if sy.len() == 0 {
        return vec!['1'];
    }
    
    if sy.len() == 1 && sy[0] == '0' {
        return vec!['1'];
    }
    
    let mut result = vec!['1'];
    let mut exp_bits = Vec::<char>::new();
    let mut base = Vec::<char>::new();
    
    let mut k = 0;
    while k < sy.len()
        invariant
            ValidBitString(exp_bits@),
            k <= sy.len(),
            ValidBitString(sy@)
    {
        exp_bits.push(sy[k]);
        k += 1;
    }
    
    k = 0;
    while k < sx.len()
        invariant
            ValidBitString(base@),
            k <= sx.len(),
            ValidBitString(sx@)
    {
        base.push(sx[k]);
        k += 1;
    }
    
    let mut i = 0;
    
    while i < exp_bits.len()
        invariant
            ValidBitString(result@),
            ValidBitString(base@),
            ValidBitString(exp_bits@),
            ValidBitString(sz@),
            i <= exp_bits.len(),
            Str2Int(sz@) > 1
    {
        if exp_bits[exp_bits.len() - 1 - i] == '1' {
            let temp = Mul(&result, &base);
            result = temp;
        }
        
        if i + 1 < exp_bits.len() {
            let temp = Mul(&base, &base);
            base = temp;
        }
        
        i += 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}
