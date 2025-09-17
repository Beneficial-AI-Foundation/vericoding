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
proof fn pow_mod_lemma(base: nat, exp: nat, modulus: nat)
    requires modulus > 1
    ensures
        exp > 0 ==> Exp_int(base, exp) % modulus == ((base % modulus) * (Exp_int(base, (exp - 1) as nat) % modulus)) % modulus
{
    if exp > 0 {
        assert(Exp_int(base, exp) == base * Exp_int(base, (exp - 1) as nat));
    }
}

proof fn exp_zero_lemma(base: nat)
    ensures Exp_int(base, 0) == 1
{
}

/* helper modified by LLM (iteration 3): added decreases clause to int_to_bitstring */
fn int_to_bitstring(n: u64) -> (res: Vec<char>)
    ensures
        ValidBitString(res@),
        Str2Int(res@) == n
{
    let mut result = Vec::new();
    if n == 0 {
        result.push('0');
        return result;
    }
    
    let mut remaining = n;
    let original_n = n;
    
    while remaining > 0
        invariant
            ValidBitString(result@),
            remaining as nat * Exp_int(2, result@.len() as nat) + Str2Int(result@) == original_n as nat
        decreases remaining
    {
        if remaining % 2 == 0 {
            result.push('0');
        } else {
            result.push('1');
        }
        remaining = remaining / 2;
    }
    result
}

fn bitstring_to_int(s: &[char]) -> (res: u64)
    requires
        ValidBitString(s@),
        Str2Int(s@) < u64::MAX
    ensures
        res == Str2Int(s@)
{
    let mut result: u64 = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            ValidBitString(s@),
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
exec fn ModExp_DivMod_ModExpPow2_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): added decreases clause to main loop */
    if sy.len() == 0 {
        proof { exp_zero_lemma(Str2Int(sx@)); }
        let mut res = Vec::new();
        res.push('1');
        return res;
    }
    
    let base_int = bitstring_to_int(sx);
    let exp_int = bitstring_to_int(sy);
    let mod_int = bitstring_to_int(sz);
    
    let mut result: u64 = 1;
    let mut base_mod = base_int % mod_int;
    let mut exp_remaining = exp_int;
    
    while exp_remaining > 0
        invariant
            mod_int == Str2Int(sz@),
            mod_int > 1,
            result < mod_int,
            base_mod < mod_int,
            (result as nat * Exp_int(base_mod as nat, exp_remaining as nat)) % (mod_int as nat) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
        decreases exp_remaining
    {
        if exp_remaining % 2 == 1 {
            result = (result * base_mod) % mod_int;
        }
        base_mod = (base_mod * base_mod) % mod_int;
        exp_remaining = exp_remaining / 2;
        
        proof { pow_mod_lemma(Str2Int(sx@), exp_remaining as nat, Str2Int(sz@)); }
    }
    
    let res = int_to_bitstring(result);
    res
}
// </vc-code>

fn main() {}
}
