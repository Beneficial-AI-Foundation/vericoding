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
proof fn lemma_exp_split(x: nat, y: nat, z: nat)
    requires y > 0, z > 0
    ensures Exp_int(x, y) % z == if y % 2 == 0 {
        (Exp_int(x, y/2) % z * Exp_int(x, y/2) % z) % z
    } else {
        (x % z * Exp_int(x, y-1) % z) % z
    }
{
    if y % 2 == 0 {
        assert(y == 2 * (y/2));
        assert(Exp_int(x, y) == Exp_int(x, 2 * (y/2)));
        assert(Exp_int(x, 2 * (y/2)) == x * Exp_int(x, 2 * (y/2) - 1));
        assert(2 * (y/2) - 1 == y - 1);
    } else {
        assert(Exp_int(x, y) == x * Exp_int(x, y - 1));
    }
}

proof fn lemma_str2int_properties(s: Seq<char>)
    requires ValidBitString(s), s.len() > 0
    ensures Str2Int(s) == 2 * Str2Int(s.subrange(0, s.len() - 1)) + if s[s.len() - 1] == '1' { 1 } else { 0 }
{
}

exec fn int_to_binary_string(mut n: u64) -> (res: Vec<char>)
    ensures ValidBitString(res@), Str2Int(res@) == n
{
    let mut result = Vec::new();
    if n == 0 {
        result.push('0');
        return result;
    }
    
    while n > 0
        invariant ValidBitString(result@)
    {
        if n % 2 == 0 {
            result.push('0');
        } else {
            result.push('1');
        }
        n = n / 2;
    }
    
    let mut reversed = Vec::new();
    let mut i: usize = result.len();
    while i > 0
        invariant 
            ValidBitString(reversed@),
            i <= result.len()
    {
        i = i - 1;
        reversed.push(result[i]);
    }
    
    reversed
}

exec fn binary_string_to_int(s: &[char]) -> (res: u64)
    requires ValidBitString(s@), s@.len() <= 64
    ensures res == Str2Int(s@)
{
    let mut result: u64 = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant 
            i <= s.len(),
            result == Str2Int(s@.subrange(0, i as int))
    {
        result = result * 2;
        if s[i] == '1' {
            result = result + 1;
        }
        i = i + 1;
    }
    
    result
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    if sy.len() == 0 {
        // This case shouldn't happen due to precondition sy@.len() > 0
        // But we handle it for completeness
        return vec!['1'];
    }
    
    let y_val = binary_string_to_int(sy);
    let z_val = binary_string_to_int(sz);
    
    if y_val == 0 {
        // x^0 = 1
        return vec!['1'];
    }
    
    if y_val == 1 {
        // x^1 mod z = x mod z
        let x_val = binary_string_to_int(sx);
        let result_val = x_val % z_val;
        return int_to_binary_string(result_val);
    }
    
    // For y > 1, we use recursion
    // If y is even: x^y mod z = (x^(y/2) mod z)^2 mod z
    // If y is odd: x^y mod z = x * x^(y-1) mod z
    
    if sy[sy.len() - 1] == '0' {
        // y is even
        let mut half_y = Vec::new();
        for i in 0..(sy.len() - 1) {
            half_y.push(sy[i]);
        }
        
        let half_result = ModExp_ModExpPow2(sx, &half_y, sz);
        let half_val = binary_string_to_int(&half_result);
        let squared = (half_val * half_val) % z_val;
        return int_to_binary_string(squared);
    } else {
        // y is odd
        let mut y_minus_1 = Vec::new();
        let mut borrow = true;
        for i in (0..sy.len()).rev() {
            if i == sy.len() - 1 && borrow {
                y_minus_1.push('0');
                borrow = false;
            } else {
                y_minus_1.push(sy[i]);
            }
        }
        y_minus_1.reverse();
        
        let rec_result = ModExp_ModExpPow2(sx, &y_minus_1, sz);
        let rec_val = binary_string_to_int(&rec_result);
        let x_val = binary_string_to_int(sx);
        let result = (x_val % z_val * rec_val) % z_val;
        return int_to_binary_string(result);
    }
}
// </vc-code>

fn main() {}
}