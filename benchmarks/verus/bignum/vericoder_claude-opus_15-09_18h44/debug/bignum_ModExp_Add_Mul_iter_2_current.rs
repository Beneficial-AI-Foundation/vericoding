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
/* helper modified by LLM (iteration 2): Added Mod function for modulo operation on bit strings */
exec fn Mod(s: &[char], m: &[char]) -> (res: Vec<char>)
    requires
        ValidBitString(s@),
        ValidBitString(m@),
        Str2Int(m@) > 0,
    ensures
        ValidBitString(res@),
        Str2Int(res@) == Str2Int(s@) % Str2Int(m@),
{
    // Simple implementation: repeatedly subtract m from s until result < m
    let mut result = s.to_vec();
    
    // Helper to check if a >= b in binary representation
    let is_greater_or_equal = |a: &Vec<char>, b: &[char]| -> bool {
        if a.len() < b.len() { return false; }
        if a.len() > b.len() { return true; }
        let mut i = a.len();
        while i > 0 {
            i = i - 1;
            if a[i] == '1' && b[i] == '0' { return true; }
            if a[i] == '0' && b[i] == '1' { return false; }
        }
        true
    };
    
    // Helper to subtract b from a (assuming a >= b)
    let subtract = |a: &Vec<char>, b: &[char]| -> Vec<char> {
        let mut result = Vec::<char>::new();
        let mut borrow = 0u8;
        let mut i = 0;
        
        while i < a.len() {
            let bit_a = if a[i] == '1' { 1u8 } else { 0u8 };
            let bit_b = if i < b.len() {
                if b[i] == '1' { 1u8 } else { 0u8 }
            } else {
                0u8
            };
            
            let diff = if bit_a >= bit_b + borrow {
                borrow = 0;
                bit_a - bit_b - borrow
            } else {
                let temp = borrow;
                borrow = 1;
                2 + bit_a - bit_b - temp
            };
            
            result.push(if diff == 1 { '1' } else { '0' });
            i = i + 1;
        }
        
        // Remove leading zeros
        while result.len() > 1 && result[result.len() - 1] == '0' {
            result.pop();
        }
        
        result
    };
    
    while is_greater_or_equal(&result, m) {
        result = subtract(&result, m);
    }
    
    if result.len() == 0 {
        result.push('0');
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
    /* code modified by LLM (iteration 2): Fixed Add implementation with proper invariants and carry handling */
    let mut carry = 0u8;
    let mut result = Vec::<char>::new();
    let mut i = 0;
    
    while i < s1.len() || i < s2.len() || carry > 0
        invariant
            0 <= i,
            i <= s1.len() || i <= s2.len() || carry > 0,
            carry <= 1,
            ValidBitString(result@),
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
        
        i = i + 1;
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
    /* code modified by LLM (iteration 2): Fixed Mul implementation with proper invariants */
    let mut result = Vec::<char>::new();
    result.push('0');
    
    let mut i = 0;
    while i < s2.len()
        invariant
            0 <= i,
            i <= s2.len(),
            ValidBitString(result@),
    {
        // Double the result
        let temp = result.clone();
        result = Add(&temp, &temp);
        
        // Add s1 if current bit of s2 is 1
        if i < s2.len() && s2[i] == '1' {
            let temp = result.clone();
            result = Add(&temp, s1);
        }
        
        i = i + 1;
    }
    
    result
}
// </vc-code>

fn main() {}
}


