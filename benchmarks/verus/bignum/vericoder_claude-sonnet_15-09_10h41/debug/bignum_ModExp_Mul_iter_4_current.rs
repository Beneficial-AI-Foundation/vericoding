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
/* helper modified by LLM (iteration 4): Fixed function placement outside method body */
fn add_binary(a: &[char], b: &[char]) -> (res: Vec<char>)
    requires ValidBitString(a@), ValidBitString(b@)
    ensures ValidBitString(res@)
{
    let mut result = Vec::<char>::new();
    let mut carry = 0;
    let mut i = 0;
    let max_len = if a.len() > b.len() { a.len() } else { b.len() };
    
    while i < max_len || carry > 0
        invariant
            ValidBitString(result@),
            carry <= 1,
            i <= max_len
    {
        let bit_a = if i < a.len() { if a[a.len() - 1 - i] == '1' { 1 } else { 0 } } else { 0 };
        let bit_b = if i < b.len() { if b[b.len() - 1 - i] == '1' { 1 } else { 0 } } else { 0 };
        let sum = bit_a + bit_b + carry;
        result.insert(0, if sum % 2 == 1 { '1' } else { '0' });
        carry = sum / 2;
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
    /* code modified by LLM (iteration 4): Fixed Mul function implementation */
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
        decreases s1.len() - i
    {
        if s1[s1.len() - 1 - i] == '1' {
            let mut shifted_s2 = Vec::<char>::new();
            let mut j = 0;
            
            while j < s2.len()
                invariant
                    ValidBitString(shifted_s2@),
                    j <= s2.len(),
                    ValidBitString(s2@)
            {
                shifted_s2.push(s2[j]);
                j += 1;
            }
            
            let mut k = 0;
            while k < i
                invariant
                    ValidBitString(shifted_s2@),
                    k <= i
            {
                shifted_s2.push('0');
                k += 1;
            }
            
            result = add_binary(&result, &shifted_s2);
        }
        
        i += 1;
    }
    
    if result.len() == 0 {
        result.push('0');
    }
    
    result
}
// </vc-code>

fn main() {}
}
