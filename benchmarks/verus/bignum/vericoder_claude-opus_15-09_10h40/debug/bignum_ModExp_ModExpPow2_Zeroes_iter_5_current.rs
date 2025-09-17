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
/* helper modified by LLM (iteration 5): Fixed type issues - use u64 for exec code instead of nat */
proof fn pow_mod_properties(x: nat, y: nat, z: nat)
    requires z > 1
    ensures
        Exp_int(x, 0nat) % z == 1nat % z,
        y > 0 ==> Exp_int(x, y) % z == ((x % z) * (Exp_int(x, (y - 1) as nat) % z)) % z
{
    if y > 0 {
        assert(Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat));
    }
}

exec fn int_to_bitstring(n: u64) -> (res: Vec<char>)
    ensures
        ValidBitString(res@),
        Str2Int(res@) == n as nat
{
    let mut result = Vec::new();
    let mut num = n;
    
    if num == 0 {
        result.push('0');
        return result;
    }
    
    while num > 0
        invariant
            ValidBitString(result@),
            Str2Int(result@) + (num as nat) * Exp_int(2, result.len() as nat) == n as nat
    {
        if num % 2 == 0 {
            result.push('0');
        } else {
            result.push('1');
        }
        num = num / 2;
    }
    
    result.reverse();
    result
}

exec fn bitstring_to_int(s: &[char]) -> (res: u64)
    requires ValidBitString(s@), Str2Int(s@) < 18446744073709551616
    ensures res as nat == Str2Int(s@)
{
    let mut result: u64 = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            i <= s.len(),
            result as nat == Str2Int(s@.subrange(0, i as int))
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
exec fn ModExp_ModExpPow2_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed type issues - use u64 for exec code instead of nat */
    let x = bitstring_to_int(sx);
    let y = bitstring_to_int(sy);
    let z = bitstring_to_int(sz);
    
    let mut base = x % z;
    let mut exp = y;
    let mut result: u64 = 1;
    
    while exp > 0
        invariant
            z > 1,
            ((result as nat) * Exp_int(base as nat, exp as nat)) % (z as nat) == Exp_int(x as nat, y as nat) % (z as nat)
    {
        if exp % 2 == 1 {
            result = (result * base) % z;
        }
        base = (base * base) % z;
        exp = exp / 2;
        
        proof {
            pow_mod_properties(x as nat, y as nat, z as nat);
        }
    }
    
    int_to_bitstring(result)
}
// </vc-code>

fn main() {}
}
