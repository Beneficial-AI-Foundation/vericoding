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
        Exp_int(x, 0nat) % z == 1nat % z,
        y > 0 ==> Exp_int(x, y) % z == ((x % z) * (Exp_int(x, (y - 1) as nat) % z)) % z
{
    if y > 0 {
        assert(Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat));
    }
}

/* helper modified by LLM (iteration 3): Fixed nat literal syntax - use 0 as nat instead of 0nat */
exec fn int_to_bitstring(n: nat) -> (res: Vec<char>)
    ensures
        ValidBitString(res@),
        Str2Int(res@) == n
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
            Str2Int(result@) + num * Exp_int(2 as nat, result.len() as nat) == n
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

exec fn bitstring_to_int(s: &[char]) -> (res: nat)
    requires ValidBitString(s@)
    ensures res == Str2Int(s@)
{
    let mut result: nat = 0;
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
exec fn ModExp_ModExpPow2_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): Fixed nat literal syntax - use 1 as nat instead of 1nat */
    let x = bitstring_to_int(sx);
    let y = bitstring_to_int(sy);
    let z = bitstring_to_int(sz);
    
    let mut base = x % z;
    let mut exp = y;
    let mut result: nat = 1;
    
    while exp > 0
        invariant
            z > 1,
            (result * Exp_int(base, exp)) % z == Exp_int(x, y) % z
    {
        if exp % 2 == 1 {
            result = (result * base) % z;
        }
        base = (base * base) % z;
        exp = exp / 2;
        
        proof {
            pow_mod_properties(x, y, z);
        }
    }
    
    int_to_bitstring(result)
}
// </vc-code>

fn main() {}
}
