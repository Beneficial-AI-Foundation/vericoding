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
/* helper modified by LLM (iteration 4): fixed type annotations and conversion issues */
proof fn exp_mod_properties(base: nat, exp: nat, modulus: nat)
    requires modulus > 1,
    ensures 
        exp == 0 ==> Exp_int(base, exp) % modulus == 1nat % modulus,
        exp > 0 ==> Exp_int(base, exp) % modulus == ((base % modulus) * (Exp_int(base % modulus, (exp - 1) as nat) % modulus)) % modulus,
    decreases exp
{
    if exp == 0 {
        assert(Exp_int(base, 0) == 1);
    } else {
        assert(Exp_int(base, exp) == base * Exp_int(base, (exp - 1) as nat));
        assert((base * Exp_int(base, (exp - 1) as nat)) % modulus == ((base % modulus) * (Exp_int(base, (exp - 1) as nat) % modulus)) % modulus);
    }
}

exec fn int_to_binary(n: nat) -> (res: Vec<char>)
    ensures 
        ValidBitString(res@),
        Str2Int(res@) == n,
    decreases n
{
    if n == 0nat {
        Vec::new()
    } else {
        let mut result = int_to_binary((n / 2) as nat);
        if n % 2nat == 0nat {
            result.push('0');
        } else {
            result.push('1');
        }
        result
    }
}

exec fn seq_to_vec(s: Seq<char>) -> (v: Vec<char>)
    ensures v@ == s
{
    let mut v = Vec::new();
    let mut i: usize = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            v@.len() == i,
            forall |j: int| 0 <= j && j < i ==> v@[j] == s[j],
    {
        v.push(s[i as int]);
        i = i + 1;
    }
    v
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): fixed type annotations and conversion issues */
    let ghost x_val = Str2Int(sx@);
    let ghost y_val = Str2Int(sy@);
    let ghost z_val = Str2Int(sz@);
    
    if sy.len() == 0 {
        proof {
            exp_mod_properties(x_val, 0nat, z_val);
        }
        return int_to_binary((1nat % z_val) as nat);
    }
    
    let ghost last_bit = sy@.index(sy@.len() - 1);
    let ghost sy_prefix = sy@.subrange(0, sy@.len() - 1);
    let ghost half_exp = (y_val / 2) as nat;
    
    let mut half_result = if sy_prefix.len() == 0 {
        int_to_binary(1nat)
    } else {
        let sy_vec: Vec<char> = seq_to_vec(sy_prefix);
        ModExp_DivMod_Zeroes(&sx[..], &sy_vec[..], &sz[..])
    };
    
    let ghost half_mod = Str2Int(half_result@);
    let ghost squared_mod = ((half_mod * half_mod) % z_val) as nat;
    
    let ghost result_val = if last_bit == '1' {
        ((squared_mod * (x_val % z_val)) % z_val) as nat
    } else {
        squared_mod
    };
    
    proof {
        exp_mod_properties(x_val, y_val, z_val);
        if last_bit == '1' {
            assert(y_val == 2 * half_exp + 1);
            assert(Exp_int(x_val, y_val) == x_val * Exp_int(x_val, (y_val - 1) as nat));
        } else {
            assert(y_val == 2 * half_exp);
            assert(Exp_int(x_val, y_val) == Exp_int(x_val, half_exp) * Exp_int(x_val, half_exp));
        }
    }
    
    return int_to_binary(result_val);
}
// </vc-code>

fn main() {}
}
