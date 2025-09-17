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
/* helper modified by LLM (iteration 5): fix type annotations for nat literals and operations */
proof fn pow_mod_lemma(base: nat, exp: nat, modulus: nat)
    requires modulus > 1,
    ensures exp == 0 ==> Exp_int(base, exp) % modulus == 1nat % modulus,
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

exec fn int_to_bitstring(n: nat) -> (res: Vec<char>)
    ensures ValidBitString(res@),
            Str2Int(res@) == n
{
    let mut result = Vec::<char>::new();
    let mut num = n;
    
    if num == 0nat {
        result.push('0');
        return result;
    }
    
    while num > 0nat
        invariant
            ValidBitString(result@),
            num <= n,
    {
        if num % 2nat == 0nat {
            result.push('0');
        } else {
            result.push('1');
        }
        num = num / 2nat;
    }
    
    let mut i = 0;
    let mut j = result.len() - 1;
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
    /* code modified by LLM (iteration 5): fix type annotations for nat literals and operations */
    let base = Str2Int(sx@);
    let exp = Str2Int(sy@);
    let modulus = Str2Int(sz@);
    
    if exp == 0nat {
        proof {
            pow_mod_lemma(base, 0nat, modulus);
        }
        return int_to_bitstring(1nat % modulus);
    }
    
    let mut result: nat = 1nat;
    let mut b: nat = base % modulus;
    let mut e = exp;
    
    while e > 0nat
        invariant
            modulus > 1,
            (result * Exp_int(b, e)) % modulus == Exp_int(base, exp) % modulus,
        decreases e
    {
        if e % 2nat == 1nat {
            result = (result * b) % modulus;
        }
        b = (b * b) % modulus;
        e = e / 2nat;
        
        proof {
            if e > 0 {
                pow_mod_lemma(b, e, modulus);
            }
        }
    }
    
    int_to_bitstring(result)
}
// </vc-code>

fn main() {}
}
