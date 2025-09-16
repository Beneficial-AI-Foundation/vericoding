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

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed problematic reverse() call and fixed bit ordering */
exec fn str_to_int(s: &[char]) -> (result: u64)
    requires ValidBitString(s@)
    ensures result as nat == Str2Int(s@)
{
    let mut res: u64 = 0;
    let mut i: usize = 0;
    while i < s.len()
        invariant 0 <= i as int <= s.len() as int,
                res as nat == Str2Int(s@.subrange(0, i as int))
    {
        if s[i] == '1' {
            res = res * 2 + 1;
        } else {
            res = res * 2;
        }
        i += 1;
    }
    res
}

/* helper modified by LLM (iteration 5): removed problematic reverse() call and fixed bit ordering */
exec fn int_to_str(n: u64) -> (result: Vec<char>)
    ensures ValidBitString(result@), Str2Int(result@) == n as nat
{
    if n == 0 {
        return vec!['0'];
    }
    
    let mut res = Vec::new();
    let mut num = n;
    let mut highest_bit = (std::mem::size_of::<u64>() * 8 - 1) as u64;
    
    // Find the highest set bit
    while highest_bit > 0 && (num >> highest_bit) == 0 {
        highest_bit -= 1;
    }
    
    // Generate bits from highest to lowest
    let mut current_bit = highest_bit;
    while current_bit > 0
        invariant current_bit >= 0,
                Str2Int(res@) << current_bit <= num as nat
        decreases current_bit
    {
        let bit_mask = 1 << (current_bit - 1);
        if num >= bit_mask {
            res.push('1');
            num -= bit_mask;
        } else {
            res.push('0');
        }
        current_bit -= 1;
    }
    
    res
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed compilation by avoiding reverse() and using corrected helpers */
{
    // Convert input strings to integers
    let x = str_to_int(sx);
    let y = str_to_int(sy);
    let z = str_to_int(sz);
    
    // Implement modular exponentiation using square-and-multiply algorithm
    let mut result: u64 = 1;
    let mut current_base: u64 = x % z;
    let mut remaining_exp: u64 = y;
    
    while remaining_exp > 0
        invariant remaining_exp >= 0,
                (result as nat * Exp_int(current_base as nat, remaining_exp as nat)) % (z as nat) == Exp_int((x % z) as nat, y as nat) % (z as nat)
        decreases remaining_exp
    {
        if remaining_exp % 2 == 1 {
            result = (result * current_base) % z;
        }
        current_base = (current_base * current_base) % z;
        remaining_exp = remaining_exp / 2;
    }
    
    // Convert the result back to a bit string
    int_to_str(result)
}
// </vc-code>

fn main() {}
}
