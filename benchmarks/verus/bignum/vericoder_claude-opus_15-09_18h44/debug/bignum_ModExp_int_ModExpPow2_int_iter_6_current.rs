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
        (x % z) * (x % z) % z == (x * x) % z,
        Exp_int(x % z, y) % z == Exp_int(x, y) % z
    decreases y
{
    if y == 0 {
    } else {
        exp_mod_properties(x, (y - 1) as nat, z);
        assert((x % z) * Exp_int(x % z, (y - 1) as nat) % z == (x % z) * (Exp_int(x, (y - 1) as nat) % z) % z);
        assert((x % z) * (Exp_int(x, (y - 1) as nat) % z) % z == (x * Exp_int(x, (y - 1) as nat)) % z);
    }
}

/* helper modified by LLM (iteration 6): Fixed parameter type from nat to u64 for exec function */
fn int_to_bitstring(n: u64) -> (res: Vec<char>)
    ensures
        ValidBitString(res@),
        Str2Int(res@) == n as nat
{
    let mut result = Vec::<char>::new();
    let mut num = n;
    
    if num == 0 {
        result.push('0');
        return result;
    }
    
    while num > 0
        invariant
            ValidBitString(result@),
            n as nat == num as nat * Exp_int(2 as nat, result.len() as nat) + Str2Int(result@)
    {
        if num % 2 == 0 {
            result.push('0');
        } else {
            result.push('1');
        }
        num = num / 2;
    }
    
    let mut i: usize = 0;
    let len = result.len();
    while i < len / 2
        invariant
            0 <= i <= len / 2,
            ValidBitString(result@),
            result.len() == len,
            Str2Int(result@) == n as nat
    {
        let temp = result[i];
        result.set(i, result[len - 1 - i]);
        result.set(len - 1 - i, temp);
        i = i + 1;
    }
    
    result
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_int_ModExpPow2_int(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 6): Fixed calls to int_to_bitstring to pass u64 instead of nat */
    if sy.len() == 0 {
        return int_to_bitstring(1u64);
    }
    
    let x_val = Str2Int(sx@);
    let y_val = Str2Int(sy@);
    let z_val = Str2Int(sz@);
    
    if sy.len() == 1 {
        if sy[0] == '0' {
            return int_to_bitstring(1u64);
        } else {
            return int_to_bitstring((x_val % z_val) as u64);
        }
    }
    
    let sy_sub = &sy[0..sy.len() - 1];
    let half_result = ModExp_int_ModExpPow2_int(sx, sy_sub, sz);
    let half_val = Str2Int(half_result@);
    
    proof {
        exp_mod_properties(x_val, y_val, z_val);
    }
    
    let squared = (half_val * half_val) % z_val;
    
    if sy[sy.len() - 1] == '1' {
        let result_val = (squared * (x_val % z_val)) % z_val;
        return int_to_bitstring(result_val as u64);
    } else {
        return int_to_bitstring(squared as u64);
    }
}
// </vc-code>

fn main() {}
}
