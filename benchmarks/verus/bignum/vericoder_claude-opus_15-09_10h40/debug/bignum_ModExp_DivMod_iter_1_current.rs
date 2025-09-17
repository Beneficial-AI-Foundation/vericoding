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
proof fn lemma_exp_properties(x: nat, y: nat, z: nat)
    requires z > 1
    ensures
        Exp_int(x, 0) == 1,
        y > 0 ==> Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat),
        Exp_int(x % z, y) % z == Exp_int(x, y) % z
{
}

proof fn lemma_mod_mul(a: nat, b: nat, m: nat)
    requires m > 0
    ensures (a * b) % m == ((a % m) * (b % m)) % m
{
}

exec fn int_to_binary(mut n: u64) -> (res: Vec<char>)
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
            n < u64::MAX
    {
        if n % 2 == 0 {
            result.push('0');
        } else {
            result.push('1');
        }
        n = n / 2;
    }
    result
}

exec fn binary_to_int(s: &[char]) -> (res: u64)
    requires
        ValidBitString(s@),
        Str2Int(s@) < u64::MAX
    ensures res == Str2Int(s@)
{
    let mut result: u64 = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result < u64::MAX
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
exec fn ModExp_DivMod(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let x_val = binary_to_int(sx);
    let y_val = binary_to_int(sy);
    let z_val = binary_to_int(sz);
    
    let mut base = x_val % z_val;
    let mut exp = y_val;
    let mut result: u64 = 1;
    
    while exp > 0
        invariant
            z_val > 1,
            result < z_val,
            base < z_val
    {
        if exp % 2 == 1 {
            proof {
                lemma_mod_mul(result, base, z_val);
            }
            result = (result * base) % z_val;
        }
        proof {
            lemma_mod_mul(base, base, z_val);
        }
        base = (base * base) % z_val;
        exp = exp / 2;
    }
    
    proof {
        lemma_exp_properties(x_val, y_val, z_val);
    }
    
    int_to_binary(result)
}
// </vc-code>

fn main() {}
}
