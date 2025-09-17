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
/* helper modified by LLM (iteration 9): use u64 instead of nat for executable code */
proof fn pow_mod_lemma(base: nat, exp: nat, modulus: nat)
    requires modulus > 1,
    ensures exp == 0 ==> Exp_int(base, exp) % modulus == 1 % modulus,
            exp > 0 ==> Exp_int(base, exp) % modulus == ((base % modulus) * (Exp_int(base, (exp - 1) as nat) % modulus)) % modulus,
    decreases exp
{
    if exp == 0 {
        assert(Exp_int(base, 0) == 1);
    } else {
        assert(Exp_int(base, exp) == base * Exp_int(base, (exp - 1) as nat));
        assert((base * Exp_int(base, (exp - 1) as nat)) % modulus == ((base % modulus) * (Exp_int(base, (exp - 1) as nat) % modulus)) % modulus);
    }
}

exec fn bitstring_to_u64(s: &[char]) -> (res: u64)
    requires ValidBitString(s@),
             s@.len() <= 64,
             Str2Int(s@) < 0x10000000000000000,
    ensures res as nat == Str2Int(s@)
{
    let mut result: u64 = 0;
    let mut i: usize = 0;
    
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            result as nat == Str2Int(s@.subrange(0, i as int)),
            ValidBitString(s@),
    {
        result = result * 2;
        if s[i] == '1' {
            result = result + 1;
        }
        i = i + 1;
    }
    
    result
}

exec fn u64_to_bitstring(n: u64) -> (res: Vec<char>)
    ensures ValidBitString(res@),
            Str2Int(res@) == n as nat
{
    let mut result = Vec::<char>::new();
    let mut num = n;
    
    if num == 0 {
        result.push('0');
        return result;
    }
    
    while num > 0
        invariant
            ValidBitString(result@),
            num <= n,
    {
        if num % 2 == 0 {
            result.push('0');
        } else {
            result.push('1');
        }
        num = num / 2;
    }
    
    let mut i: usize = 0;
    let mut j: usize = if result.len() > 0 { result.len() - 1 } else { 0 };
    while i < j
        invariant
            0 <= i <= j < result.len(),
            ValidBitString(result@),
    {
        let temp = result[i];
        result.set(i, result[j]);
        result.set(j, temp);
        i = i + 1;
        j = j - 1;
    }
    
    result
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 9): use u64 instead of nat for executable code */
    let base_u64 = bitstring_to_u64(sx);
    let exp_u64 = bitstring_to_u64(sy);
    let modulus_u64 = bitstring_to_u64(sz);
    
    if exp_u64 == 0 {
        proof {
            pow_mod_lemma(base_u64 as nat, 0 as nat, modulus_u64 as nat);
        }
        let mod_result = 1 % modulus_u64;
        return u64_to_bitstring(mod_result);
    }
    
    let mut result: u64 = 1;
    let mut b: u64 = base_u64 % modulus_u64;
    let mut e = exp_u64;
    
    while e > 0
        invariant
            modulus_u64 > 1,
            ((result as nat) * Exp_int(b as nat, e as nat)) % (modulus_u64 as nat) == Exp_int(base_u64 as nat, exp_u64 as nat) % (modulus_u64 as nat),
        decreases e
    {
        if e % 2 == 1 {
            result = (result * b) % modulus_u64;
        }
        b = (b * b) % modulus_u64;
        e = e / 2;
        
        proof {
            if e > 0 {
                pow_mod_lemma(b as nat, e as nat, modulus_u64 as nat);
            }
        }
    }
    
    u64_to_bitstring(result)
}
// </vc-code>

fn main() {}
}
