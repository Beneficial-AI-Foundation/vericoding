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
    requires
        z > 1
    ensures
        Exp_int(x, 0) % z == 1nat % z,
        y > 0 ==> Exp_int(x, y) % z == ((x % z) * (Exp_int(x, (y - 1) as nat) % z)) % z
{
    if y > 0 {
        assert(Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat));
    }
}

fn int_to_binary(n: nat) -> (res: Vec<char>)
    ensures
        ValidBitString(res@),
        Str2Int(res@) == n
{
    let mut result = Vec::new();
    let mut num = n;
    
    if num == 0nat {
        result.push('0');
        return result;
    }
    
    while num > 0nat
        invariant
            ValidBitString(result@),
            Str2Int(result@) + num * Exp_int(2, result.len() as nat) == n
    {
        if num % 2nat == 0nat {
            result.push('0');
        } else {
            result.push('1');
        }
        num = num / 2nat;
    }
    
    result.reverse();
    result
}

fn mod_mult(a: nat, b: nat, m: nat) -> (res: nat)
    requires
        m > 1
    ensures
        res == (a * b) % m,
        res < m
{
    ((a % m) * (b % m)) % m
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): fixed type issues with nat literals and seq indexing */
    let x = Str2Int(sx@);
    let y = Str2Int(sy@);
    let z = Str2Int(sz@);
    
    if sy@.len() == 1nat {
        if sy@.index(0int) == '0' {
            proof { exp_mod_properties(x, 0, z); }
            return int_to_binary((1nat % z) as nat);
        } else {
            return int_to_binary(x % z);
        }
    }
    
    let sy_len = sy.len();
    let sy_prefix = sy@.subrange(0int, (sy_len - 1) as int);
    let mut sy_vec = Vec::new();
    let prefix_len = sy_len - 1;
    for i in 0..prefix_len {
        sy_vec.push(sy[i]);
    }
    
    let half_result = ModExp_Add_Zeroes(sx, &sy_vec, sz);
    let half_val = Str2Int(half_result@);
    
    let squared = mod_mult(half_val, half_val, z);
    
    let result = if sy[sy_len - 1] == '1' {
        mod_mult(squared, x % z, z)
    } else {
        squared
    };
    
    proof { exp_mod_properties(x, y, z); }
    
    int_to_binary(result)
}
// </vc-code>

fn main() {}
}
