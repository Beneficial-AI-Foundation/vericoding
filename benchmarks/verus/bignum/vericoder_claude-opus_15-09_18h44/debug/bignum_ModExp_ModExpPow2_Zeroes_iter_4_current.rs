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
proof fn pow_mod_properties(x: nat, y: nat, z: nat)
    requires z > 1
    ensures
        y == 0 ==> Exp_int(x, y) % z == 1nat % z,
        y > 0 ==> Exp_int(x, y) % z == ((x % z) * (Exp_int(x, (y - 1) as nat) % z)) % z
{
    if y == 0 {
        assert(Exp_int(x, y) == 1);
    } else {
        assert(Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat));
    }
}

exec fn int_to_binary(mut n: u64) -> (res: Vec<char>)
    ensures
        ValidBitString(res@),
        Str2Int(res@) == n
{
    let mut result = Vec::new();
    if n == 0 {
        result.push('0');
    } else {
        let mut temp = Vec::new();
        let mut num = n;
        while num > 0
            invariant
                ValidBitString(temp@)
        {
            if num % 2 == 0 {
                temp.push('0');
            } else {
                temp.push('1');
            }
            num = num / 2;
        }
        let mut i = temp.len();
        while i > 0
            invariant
                ValidBitString(result@),
                0 <= i <= temp.len()
        {
            i = i - 1;
            result.push(temp[i]);
        }
    }
    result
}

exec fn mod_mult(a: u64, b: u64, m: u64) -> (res: u64)
    requires m > 0
    ensures res == (a as nat * b as nat) % m as nat
{
    ((a % m) * (b % m)) % m
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Fixed type mismatches with nat literals and casting */
{
    if sy@.len() == 0nat {
        return int_to_binary(1);
    }
    
    let x_val = Str2Int(sx@);
    let y_val = Str2Int(sy@);
    let z_val = Str2Int(sz@);
    
    if y_val == 0nat {
        proof {
            pow_mod_properties(x_val, 0nat, z_val);
        }
        return int_to_binary((1nat % z_val) as u64);
    }
    
    let mut y_minus_one = Vec::new();
    let mut i: nat = 0nat;
    let mut carry = true;
    while i < sy@.len()
        invariant
            0 <= i <= sy@.len(),
            ValidBitString(y_minus_one@)
    {
        if i == sy@.len() - 1nat && sy[i as usize] == '1' {
            i = i + 1nat;
        } else if sy[i as usize] == '0' && carry {
            i = i + 1nat;
        } else {
            i = i + 1nat;
            carry = false;
        }
    }
    
    let rec_result = ModExp_ModExpPow2_Zeroes(sx, &y_minus_one, sz);
    let rec_val = Str2Int(rec_result@);
    
    proof {
        pow_mod_properties(x_val, y_val, z_val);
    }
    
    let result_val = mod_mult((x_val % z_val) as u64, rec_val as u64, z_val as u64);
    return int_to_binary(result_val);
}
// </vc-code>

fn main() {}
}
