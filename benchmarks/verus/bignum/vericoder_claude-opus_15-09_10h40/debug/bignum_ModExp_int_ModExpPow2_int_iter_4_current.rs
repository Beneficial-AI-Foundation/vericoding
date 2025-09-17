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
/* helper modified by LLM (iteration 4): fixed index method not found error by using bracket notation */
proof fn exp_mod_properties(x: nat, y: nat, z: nat)
    requires z > 0
    ensures
        (x * x) % z == ((x % z) * (x % z)) % z,
        (x * y) % z == ((x % z) * (y % z)) % z
{ }

proof fn str2int_properties(s: Seq<char>)
    requires ValidBitString(s)
    ensures
        s.len() > 0 ==> Str2Int(s) < Exp_int(2, s.len()),
        Str2Int(s) >= 0
    decreases s.len()
{
    if s.len() > 0 {
        str2int_properties(s.subrange(0, s.len() as int - 1));
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
        return result;
    }
    
    while n > 0
        invariant
            ValidBitString(result@)
    {
        if n % 2 == 0 {
            result.push('0');
        } else {
            result.push('1');
        }
        n = n / 2;
    }
    
    let mut i: usize = 0;
    let mut j: usize = result.len() - 1;
    while i < j
        invariant
            ValidBitString(result@),
            0 <= i <= j < result.len()
    {
        let temp = result[i];
        result.set(i, result[j]);
        result.set(j, temp);
        i = i + 1;
        j = j - 1;
    }
    
    result
}

exec fn binary_to_int(s: &[char]) -> (res: u64)
    requires
        ValidBitString(s@),
        s@.len() <= 64
    ensures
        res == Str2Int(s@)
{
    let mut result: u64 = 0;
    let mut power: u64 = 1;
    let mut i: usize = s.len();
    
    while i > 0
        invariant
            0 <= i <= s.len(),
            ValidBitString(s@)
        decreases i
    {
        i = i - 1;
        if s[i] == '1' {
            result = result + power;
        }
        if i > 0 {
            power = power * 2;
        }
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
    /* code modified by LLM (iteration 4): implementation unchanged */
    let z_val = binary_to_int(sz);
    
    if sy.len() == 1 && sy[0] == '0' {
        return int_to_binary(1);
    }
    
    let x_val = binary_to_int(sx) % z_val;
    let mut result: u64 = 1;
    let mut base = x_val;
    
    let mut i: usize = sy.len();
    while i > 0
        invariant
            0 <= i <= sy.len(),
            ValidBitString(sy@),
            base < z_val,
            result < z_val
        decreases i
    {
        i = i - 1;
        if sy[i] == '1' {
            result = (result * base) % z_val;
        }
        if i > 0 {
            base = (base * base) % z_val;
        }
    }
    
    int_to_binary(result)
}
// </vc-code>

fn main() {}
}
