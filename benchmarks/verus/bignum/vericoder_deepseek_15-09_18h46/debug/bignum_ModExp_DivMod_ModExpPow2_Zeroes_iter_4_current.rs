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
/* helper modified by LLM (iteration 4): Add helper functions for correct integer conversion */
proof fn mod_mul_property(a: nat, b: nat, m: nat) 
    requires m > 1
    ensures (a * b) % m == ((a % m) * (b % m)) % m
{}

proof fn exp_mod_property(base: nat, exp: nat, m: nat)
    requires m > 1
    ensures Exp_int(base, exp) % m == Exp_int(base % m, exp) % m
{
    if exp > 0 {
        exp_mod_property(base, (exp - 1) as nat, m);
    }
}

proof fn int_conversion_lemma(n: nat) 
    ensures n as int == n as int && n as int >= 0 
{}

fn to_int(n: nat) -> (res: int)
    ensures res == n as int && res >= 0
{
    n as int
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Fix int/nat conversion errors and use proper modulus calculation */
{
    let x = Str2Int(sx@);
    let y = Str2Int(sy@);
    let z = Str2Int(sz@);
    
    proof {
        exp_mod_property(x, y, z);
    }
    
    let base_mod = x % z;
    let mut result = 1nat;
    let mut current = base_mod;
    let mut exp = y;
    
    while exp > 0
        invariant
            result == Exp_int(base_mod, y - exp) % z,
            current == Exp_int(base_mod, Exp_int(2, y - exp)) % z,
            exp <= y
        decreases exp
    {
        if exp % 2 == 1 {
            result = (result * current) % z;
        }
        current = (current * current) % z;
        exp = exp / 2;
    }
    
    let mut res_vec = Vec::<char>::new();
    let mut remainder = result;
    
    while remainder > 0
        invariant
            ValidBitString(res_vec@),
            Str2Int(res_vec@) == remainder
    {
        if remainder % 2 == 1 {
            res_vec.push('1');
        } else {
            res_vec.push('0');
        }
        remainder = remainder / 2;
    }
    
    if res_vec.is_empty() {
        res_vec.push('0');
    } else {
        res_vec.reverse();
    }
    
    res_vec
}
// </vc-code>

fn main() {}
}
