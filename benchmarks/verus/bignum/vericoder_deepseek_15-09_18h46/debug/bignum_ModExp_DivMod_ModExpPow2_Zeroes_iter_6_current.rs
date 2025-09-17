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
/* helper modified by LLM (iteration 6): Fix nat/int type mismatches and add proper conversion helpers */
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

proof fn nat_sub_lemma(a: nat, b: nat)
    requires b <= a
    ensures (a - b) as nat == a - b
{}

proof fn nat_div_lemma(n: nat, d: nat)
    requires d > 0
    ensures (n / d) as nat == n / d
{}

proof fn nat_mod_lemma(n: nat, d: nat)
    requires d > 0
    ensures (n % d) as nat == n % d
{}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 6): Fix nat/int type mismatches and use proper conversions */
{
    let x = Str2Int(sx@);
    let y = Str2Int(sy@);
    let z = Str2Int(sz@);
    
    proof {
        exp_mod_property(x, y, z);
    }
    
    let base_mod = x % z;
    let mut result: nat = 1;
    let mut current: nat = base_mod;
    let mut exp: nat = y;
    
    while exp > 0
        invariant
            result == Exp_int(base_mod, y - exp) % z,
            current == Exp_int(base_mod, Exp_int(2, y - exp)) % z,
            exp <= y
        decreases exp
    {
        proof {
            nat_mod_lemma(exp, 2);
            nat_div_lemma(exp, 2);
            nat_sub_lemma(y, exp);
        }
        
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
        proof {
            nat_mod_lemma(remainder, 2);
            nat_div_lemma(remainder, 2);
        }
        
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
