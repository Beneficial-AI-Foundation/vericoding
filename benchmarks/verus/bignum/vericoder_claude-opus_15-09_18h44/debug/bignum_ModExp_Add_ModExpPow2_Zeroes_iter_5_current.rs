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
        assert(Exp_int(x, 0) == 1);
    } else {
        assert(Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat));
    }
}

fn char_to_bit(c: char) -> (b: u8)
    ensures 
        b == 0 || b == 1,
        c == '0' ==> b == 0,
        c == '1' ==> b == 1
{
    if c == '0' { 0 } else { 1 }
}

/* helper modified by LLM (iteration 5): fixed nat literal types */
fn int_to_bitstring(n: nat) -> (res: Vec<char>)
    ensures 
        ValidBitString(res@),
        Str2Int(res@) == n
    decreases n
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
            num >= 0,
        decreases num
    {
        if num % 2nat == 0nat {
            result.push('0');
        } else {
            result.push('1');
        }
        num = num / 2nat;
    }
    
    let mut i: usize = 0;
    let mut j = result.len() - 1;
    while i < j
        invariant
            0 <= i <= j < result.len(),
            ValidBitString(result@),
        decreases j - i
    {
        let temp = result[i];
        result.set(i, result[j]);
        result.set(j, temp);
        i = i + 1;
        j = j - 1;
    }
    
    result
}

/* helper modified by LLM (iteration 5): fixed nat literal types */
fn bitstring_to_int(s: &[char]) -> (n: nat)
    requires ValidBitString(s@)
    ensures n == Str2Int(s@)
    decreases s@.len()
{
    let mut result: nat = 0nat;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            ValidBitString(s@),
        decreases s.len() - i
    {
        result = result * 2nat;
        if s[i] == '1' {
            result = result + 1nat;
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
    /* code modified by LLM (iteration 5): fixed nat literal types */
    let x_val = bitstring_to_int(sx);
    let y_val = bitstring_to_int(sy);
    let z_val = bitstring_to_int(sz);
    
    let mut result: nat = 1nat;
    let mut base = x_val % z_val;
    let mut exp = y_val;
    
    while exp > 0nat
        invariant
            z_val > 1,
            result >= 0,
            base >= 0,
            exp >= 0,
        decreases exp
    {
        if exp % 2nat == 1nat {
            result = (result * base) % z_val;
        }
        base = (base * base) % z_val;
        exp = exp / 2nat;
    }
    
    proof {
        pow_mod_properties(x_val, y_val, z_val);
    }
    
    int_to_bitstring(result)
}
// </vc-code>

fn main() {}
}
