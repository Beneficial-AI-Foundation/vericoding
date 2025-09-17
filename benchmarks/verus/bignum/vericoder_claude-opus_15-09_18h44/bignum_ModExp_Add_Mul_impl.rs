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
    /* code modified by LLM (iteration 10): Fix Add implementation with proper invariants */
    let mut carry = 0u8;
    let mut result = Vec::<char>::new();
    let mut i = 0usize;
    
    let max_len = if s1.len() > s2.len() { s1.len() } else { s2.len() };
    
    while i < max_len || carry > 0
        invariant
            0 <= i,
            i <= max_len + 1,
            carry <= 1,
            ValidBitString(result@),
            result.len() == i,
            i <= max_len ==> i <= s1.len() || i <= s2.len(),
        decreases max_len + 1 - i
    {
        let bit1 = if i < s1.len() { 
            if s1[i] == '1' { 1u8 } else { 0u8 }
        } else { 
            0u8 
        };
        
        let bit2 = if i < s2.len() { 
            if s2[i] == '1' { 1u8 } else { 0u8 }
        } else { 
            0u8 
        };
        
        let sum = bit1 + bit2 + carry;
        carry = sum / 2;
        let bit = sum % 2;
        
        if bit == 1 {
            result.push('1');
        } else {
            result.push('0');
        }
        
        if i < max_len {
            i = i + 1;
        } else {
            break;
        }
    }
    
    result
}
// </vc-code>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): Implement multiplication by bit shifting */
    let mut result = Vec::<char>::new();
    result.push('0');
    
    // Process s2 from MSB to LSB
    if s2.len() > 0 {
        let mut i = s2.len() - 1;
        loop
            invariant
                ValidBitString(result@),
            decreases i + 1
        {
            // Double the result
            let temp = result.clone();
            result = Add(&temp, &temp);
            
            // Add s1 if current bit is 1
            if s2[i] == '1' {
                let temp = result.clone();
                result = Add(&temp, s1);
            }
            
            if i == 0 {
                break;
            }
            i = i - 1;
        }
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
    /* code modified by LLM (iteration 10): Simple modular exponentiation */
    // Handle base case: y = 0, return 1
    if sy.len() == 1 && sy[0] == '0' {
        let mut result = Vec::<char>::new();
        result.push('1');
        return result;
    }
    
    // Initialize result to 1
    let mut result = Vec::<char>::new();
    result.push('1');
    
    // Initialize base
    let mut base = Vec::<char>::new();
    let mut j = 0usize;
    while j < sx.len()
        invariant
            0 <= j,
            j <= sx.len(),
            base.len() == j,
            ValidBitString(base@),
        decreases sx.len() - j
    {
        base.push(sx[j]);
        j = j + 1;
    }
    
    // Process sy bit by bit from LSB to MSB
    let mut i = 0usize;
    while i < sy.len()
        invariant
            0 <= i,
            i <= sy.len(),
            ValidBitString(result@),
        decreases sy.len() - i
    {
        // If current bit is 1, multiply result by base
        if sy[i] == '1' {
            let temp = result.clone();
            result = Mul(&temp, &base);
        }
        
        // Square the base for next bit (if not last)
        if i + 1 < sy.len() {
            let temp = base.clone();
            base = Mul(&temp, &temp);
        }
        
        i = i + 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}


