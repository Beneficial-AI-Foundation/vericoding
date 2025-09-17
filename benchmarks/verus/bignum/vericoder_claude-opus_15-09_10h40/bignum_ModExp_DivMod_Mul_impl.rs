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
proof fn exp_mod_properties(x: nat, y: nat, z: nat)
    requires z > 1
    ensures
        y == 0 ==> Exp_int(x, y) % z == 1nat % z,
        y > 0 ==> Exp_int(x, y) % z == ((x % z) * (Exp_int(x, (y - 1) as nat) % z)) % z
{
    if y == 0 {
        assert(Exp_int(x, 0) == 1);
    } else {
        assert(Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat));
    }
}

exec fn int_to_bitstring(mut n: u64) -> (res: Vec<char>)
    ensures
        ValidBitString(res@),
        Str2Int(res@) == n
{
    let mut result = Vec::new();
    if n == 0 {
        result.push('0');
        return result;
    }
    
    while n > 0
        invariant
            ValidBitString(result@),
            n > 0 ==> result@.len() < 64
    {
        if n % 2 == 1 {
            result.push('1');
        } else {
            result.push('0');
        }
        n = n / 2;
    }
    result
}

/* helper modified by LLM (iteration 5): Fixed nat literal syntax error */
exec fn bitstring_div_2(s: &[char]) -> (res: Vec<char>)
    requires
        ValidBitString(s@),
        s@.len() > 0
    ensures
        ValidBitString(res@),
        Str2Int(res@) == Str2Int(s@) / 2
{
    if s@.len() == 1 {
        let mut result = Vec::new();
        result.push('0');
        return result;
    }
    
    let mut result = Vec::new();
    for i in 0..(s.len() - 1)
        invariant
            ValidBitString(result@),
            result@.len() == i,
            forall |j: int| 0 <= j && j < i ==> result@[j] == s@[j]
    {
        result.push(s[i]);
    }
    result
}

exec fn mod_multiply(a: u64, b: u64, m: u64) -> (res: u64)
    requires m > 1
    ensures res == (a as nat * b as nat) % (m as nat)
{
    ((a % m) * (b % m)) % m
}

exec fn bitstring_to_u64(s: &[char]) -> (res: u64)
    requires
        ValidBitString(s@),
        Str2Int(s@) < 0x10000000000000000
    ensures
        res as nat == Str2Int(s@)
{
    let mut result: u64 = 0;
    let mut power: u64 = 1;
    
    for i in 0..s.len()
        invariant
            0 <= i <= s.len(),
            power == (1u64 << i),
            result as nat == Str2Int(s@.subrange(0, i as int))
    {
        if s[i] == '1' {
            result = result + power;
        }
        if i < s.len() - 1 {
            power = power * 2;
        }
    }
    result
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Implementation unchanged from iteration 4 */
    if sy.len() == 0 || (sy.len() == 1 && sy[0] == '0') {
        proof {
            exp_mod_properties(Str2Int(sx@), 0, Str2Int(sz@));
        }
        let sz_val = bitstring_to_u64(sz);
        let one_val = 1u64 % sz_val;
        return int_to_bitstring(one_val);
    }
    
    let last_bit = sy[sy.len() - 1];
    let sy_div_2 = bitstring_div_2(sy);
    
    let half_result = ModExp_DivMod_Mul(&sx, &sy_div_2, &sz);
    let half_val = bitstring_to_u64(&half_result);
    let sz_val = bitstring_to_u64(sz);
    
    let mut result_val = mod_multiply(half_val, half_val, sz_val);
    
    if last_bit == '1' {
        let sx_val = bitstring_to_u64(sx);
        result_val = mod_multiply(result_val, sx_val, sz_val);
    }
    
    proof {
        if last_bit == '1' {
            exp_mod_properties(Str2Int(sx@), Str2Int(sy@), Str2Int(sz@));
        } else {
            exp_mod_properties(Str2Int(sx@), Str2Int(sy@), Str2Int(sz@));
        }
    }
    
    int_to_bitstring(result_val)
}
// </vc-code>

fn main() {}
}
