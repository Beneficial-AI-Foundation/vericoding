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
/* helper modified by LLM (iteration 10): Binary addition helper with proper overflow handling */
fn add_binary(a: &[char], b: &[char]) -> (res: Vec<char>)
    requires ValidBitString(a@), ValidBitString(b@)
    ensures ValidBitString(res@)
{
    let mut result = Vec::new();
    let mut carry = 0;
    let max_len = if a.len() > b.len() { a.len() } else { b.len() };
    
    let mut i = 0;
    while i < max_len
        invariant
            i <= max_len,
            carry == 0 || carry == 1,
            ValidBitString(result@)
    {
        let a_bit = if i < a.len() { if a[a.len() - 1 - i] == '1' { 1 } else { 0 } } else { 0 };
        let b_bit = if i < b.len() { if b[b.len() - 1 - i] == '1' { 1 } else { 0 } } else { 0 };
        let sum = a_bit + b_bit + carry;
        result.insert(0, if sum % 2 == 1 { '1' } else { '0' });
        carry = if sum >= 2 { 1 } else { 0 };
        i += 1;
    }
    
    if carry > 0 {
        result.insert(0, '1');
    }
    
    result
}

/* helper modified by LLM (iteration 10): Binary subtraction helper with proper underflow handling */
fn sub_binary(a: &[char], b: &[char]) -> (res: Vec<char>)
    requires ValidBitString(a@), ValidBitString(b@)
    ensures ValidBitString(res@)
{
    let mut result = Vec::new();
    let mut borrow = 0;
    
    let mut i = 0;
    while i < a.len()
        invariant
            i <= a.len(),
            borrow == 0 || borrow == 1,
            ValidBitString(result@)
    {
        let a_bit = if a[a.len() - 1 - i] == '1' { 1 } else { 0 };
        let b_bit = if i < b.len() { if b[b.len() - 1 - i] == '1' { 1 } else { 0 } } else { 0 };
        
        if a_bit >= b_bit + borrow {
            result.insert(0, if a_bit - b_bit - borrow == 1 { '1' } else { '0' });
            borrow = 0;
        } else {
            result.insert(0, if a_bit + 2 - b_bit - borrow == 1 { '1' } else { '0' });
            borrow = 1;
        }
        i += 1;
    }
    
    while result.len() > 1 && result[0] == '0'
        invariant
            ValidBitString(result@),
            result.len() > 0
    {
        result.remove(0);
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
    /* code modified by LLM (iteration 10): simplified multiplication using helper functions */
    let zero = vec!['0'];
    let one = vec!['1'];
    
    if s1.len() == 0 || s2.len() == 0 {
        return zero;
    }
    
    if (s1.len() == 1 && s1[0] == '0') || (s2.len() == 1 && s2[0] == '0') {
        return zero;
    }
    
    if s1.len() == 1 && s1[0] == '1' {
        return s2.to_vec();
    }
    
    if s2.len() == 1 && s2[0] == '1' {
        return s1.to_vec();
    }
    
    let mut result = zero.clone();
    
    let mut i = 0;
    while i < s2.len()
        invariant
            i <= s2.len(),
            ValidBitString(result@)
        decreases s2.len() - i
    {
        if s2[s2.len() - 1 - i] == '1' {
            let mut shifted = s1.to_vec();
            
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
            
            result = add_binary(&result, &shifted);
        }
        i += 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}
