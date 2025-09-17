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
proof fn lemma_exp_properties(x: nat, y: nat)
    ensures
        y > 0 ==> Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat),
        Exp_int(x, 0) == 1,
{
}

proof fn lemma_str2int_properties(s: Seq<char>)
    requires
        ValidBitString(s),
    ensures
        s.len() > 0 ==> Str2Int(s) == 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat }),
        s.len() == 0 ==> Str2Int(s) == 0,
{
}

exec fn int_to_bitstring(mut n: u64) -> (res: Vec<char>)
    ensures
        ValidBitString(res@),
        Str2Int(res@) == n,
{
    let mut result = Vec::new();
    if n == 0 {
        result.push('0');
        return result;
    }
    
    while n > 0
        invariant
            ValidBitString(result@),
    {
        if n % 2 == 1 {
            result.push('1');
        } else {
            result.push('0');
        }
        n = n / 2;
    }
    
    let mut i: usize = 0;
    let mut j: usize = result.len() - 1;
    
    while i < j
        invariant
            ValidBitString(result@),
            0 <= i <= result.len(),
            j < result.len(),
    {
        let temp = result[i];
        result.set(i, result[j]);
        result.set(j, temp);
        i = i + 1;
        j = j - 1;
    }
    
    result
}

exec fn modular_multiply(a: u64, b: u64, m: u64) -> (res: u64)
    requires
        m > 0,
    ensures
        res == (a as nat * b as nat) % (m as nat),
{
    ((a as u128 * b as u128) % m as u128) as u64
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    if sy@.len() == 0 {
        return int_to_bitstring(1);
    }
    
    let x_val = Str2Int(sx@) as u64;
    let y_val = Str2Int(sy@) as u64;
    let z_val = Str2Int(sz@) as u64;
    
    let mut result: u64 = 1;
    let mut base = x_val % z_val;
    let mut exp = y_val;
    
    while exp > 0
        invariant
            z_val > 1,
    {
        if exp % 2 == 1 {
            result = modular_multiply(result, base, z_val);
        }
        base = modular_multiply(base, base, z_val);
        exp = exp / 2;
    }
    
    int_to_bitstring(result)
}
// </vc-code>

fn main() {}
}
