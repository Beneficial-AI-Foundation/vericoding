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
{
    /* code modified by LLM (iteration 5): add decreases clause to fix compilation error */
    let mut result = Vec::<char>::new();
    let mut carry = 0;
    let mut i = 0;
    let len1 = s1.len();
    let len2 = s2.len();
    let max_len = if len1 > len2 { len1 } else { len2 };
    
    while i < max_len || carry > 0
        invariant
            i <= max_len,
            carry <= 1,
            ValidBitString(result@)
        decreases max_len + 1 - i + carry
    {
        let bit1 = if i < len1 { if s1[len1 - 1 - i] == '1' { 1 } else { 0 } } else { 0 };
        let bit2 = if i < len2 { if s2[len2 - 1 - i] == '1' { 1 } else { 0 } } else { 0 };
        let sum = bit1 + bit2 + carry;
        let result_bit = if sum % 2 == 1 { '1' } else { '0' };
        result.push(result_bit);
        carry = sum / 2;
        i += 1;
    }
    
    let mut reversed = Vec::<char>::new();
    let mut j = result.len();
    while j > 0
        invariant
            j <= result.len(),
            ValidBitString(reversed@)
        decreases j
    {
        j -= 1;
        reversed.push(result[j]);
    }
    
    if reversed.len() == 0 {
        reversed.push('0');
    }
    reversed
}
// </vc-code>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): maintain existing implementation from iteration 4 */
    if s1.len() == 0 || s2.len() == 0 {
        let mut result = Vec::<char>::new();
        result.push('0');
        return result;
    }
    
    let mut result = Vec::<char>::new();
    result.push('0');
    
    let mut i = 0;
    while i < s2.len()
        invariant
            i <= s2.len(),
            ValidBitString(result@)
        decreases s2.len() - i
    {
        if s2[s2.len() - 1 - i] == '1' {
            let mut shifted = Vec::<char>::new();
            let mut j = 0;
            while j < i
                invariant
                    j <= i,
                    ValidBitString(shifted@)
                decreases i - j
            {
                shifted.push('0');
                j += 1;
            }
            for k in 0..s1.len() {
                shifted.push(s1[k]);
            }
            proof {
                assert(ValidBitString(s1@));
                assert(ValidBitString(shifted@));
            }
            result = Add(&result, &shifted);
        }
        i += 1;
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
    /* code modified by LLM (iteration 5): maintain existing implementation from iteration 4 */
    if sy.len() == 0 {
        let mut result = Vec::<char>::new();
        result.push('1');
        return result;
    }
    
    if sy.len() == 1 && sy[0] == '0' {
        let mut result = Vec::<char>::new();
        result.push('1');
        return result;
    }
    
    let mut base = Vec::<char>::new();
    for i in 0..sx.len() {
        base.push(sx[i]);
    }
    
    let mut result = Vec::<char>::new();
    result.push('1');
    
    let mut i = 0;
    while i < sy.len()
        invariant
            i <= sy.len(),
            ValidBitString(result@),
            ValidBitString(base@)
        decreases sy.len() - i
    {
        if sy[sy.len() - 1 - i] == '1' {
            proof {
                assert(ValidBitString(result@));
                assert(ValidBitString(base@));
            }
            result = Mul(&result, &base);
        }
        if i + 1 < sy.len() {
            proof {
                assert(ValidBitString(base@));
            }
            base = Mul(&base, &base);
        }
        i += 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}


