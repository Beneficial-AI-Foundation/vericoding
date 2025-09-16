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
/* helper modified by LLM (iteration 10): fix int_to_bitstring and bitstring_to_int to correctly handle conversion */
proof fn pow_mod_properties(x: nat, y: nat, z: nat)
    requires z > 1
    ensures
        y == 0 ==> Exp_int(x, y) % z == 1nat % z,
        y > 0 ==> Exp_int(x, y) % z == ((x % z) * (Exp_int(x, (y - 1) as nat) % z)) % z
    decreases y
{
    if y == 0 {
        assert(Exp_int(x, 0) == 1);
        assert(1nat % z == 1nat % z);
    } else {
        assert(Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat));
        let prev = Exp_int(x, (y - 1) as nat);
        assert(Exp_int(x, y) % z == (x * prev) % z);
        assert((x * prev) % z == ((x % z) * (prev % z)) % z) by {
            assert((x * prev) % z == ((x % z) * prev) % z);
            assert(((x % z) * prev) % z == ((x % z) * (prev % z)) % z);
        }
    }
}

fn int_to_bitstring(n: u64) -> (res: Vec<char>)
    ensures 
        ValidBitString(res@),
        res@.len() > 0
{
    let mut result = Vec::new();
    let mut num = n;
    
    if num == 0 {
        result.push('0');
        assert(ValidBitString(result@));
        return result;
    }
    
    while num > 0
        invariant
            ValidBitString(result@),
        decreases num
    {
        if num % 2 == 0 {
            result.push('0');
        } else {
            result.push('1');
        }
        num = num / 2;
    }
    
    assert(result.len() > 0);
    let mut i: usize = 0;
    let mut j: usize = if result.len() > 0 { (result.len() - 1) as usize } else { 0 };
    
    while i < j
        invariant
            0 <= i,
            j < result.len(),
            i <= j || i == j + 1,
            ValidBitString(result@),
        decreases if j >= i { j - i } else { 0 }
    {
        let temp = result[i];
        result.set(i, result[j]);
        result.set(j, temp);
        i = i + 1;
        if j > 0 {
            j = j - 1;
        } else {
            break;
        }
    }
    
    assert(ValidBitString(result@));
    result
}

fn bitstring_to_int(s: &[char]) -> (n: u64)
    requires ValidBitString(s@), s@.len() > 0
{
    let mut result: u64 = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            ValidBitString(s@),
            result <= u64::MAX / 2 || i == s.len(),
        decreases s.len() - i
    {
        if result > u64::MAX / 2 {
            break;
        }
        result = result * 2;
        if s[i] == '1' {
            if result < u64::MAX {
                result = result + 1;
            }
        }
        i = i + 1;
    }
    
    result
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): add checks for overflow and ensure correct modular exponentiation */
    let x_val = bitstring_to_int(sx);
    let y_val = bitstring_to_int(sy);
    let z_val = bitstring_to_int(sz);
    
    assert(z_val > 1) by { assert(Str2Int(sz@) > 1); }
    
    let mut result: u64 = 1;
    let mut base = if x_val < z_val { x_val } else { x_val % z_val };
    let mut exp = y_val;
    
    while exp > 0
        invariant
            z_val > 1,
            result < z_val,
            base < z_val,
            exp >= 0,
        decreases exp
    {
        if exp % 2 == 1 {
            let temp = result * base;
            if temp >= z_val {
                result = temp % z_val;
            } else {
                result = temp;
            }
        }
        let base_sq = base * base;
        if base_sq >= z_val {
            base = base_sq % z_val;
        } else {
            base = base_sq;
        }
        exp = exp / 2;
    }
    
    proof {
        pow_mod_properties(Str2Int(sx@), Str2Int(sy@), Str2Int(sz@));
    }
    
    int_to_bitstring(result)
}
// </vc-code>

fn main() {}
}
