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
/* helper modified by LLM (iteration 3): fixed type annotations for nat literals */
proof fn lemma_exp_properties(x: nat, y: nat)
    ensures
        y > 0 ==> Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat),
        Exp_int(x, 0) == 1
{
}

proof fn lemma_modexp_base(x: nat, z: nat)
    requires z > 1
    ensures Exp_int(x, 0) % z == 1nat % z
{
}

proof fn lemma_modexp_recursive(x: nat, y: nat, z: nat)
    requires
        y > 0,
        z > 1
    ensures Exp_int(x, y) % z == ((x % z) * (Exp_int(x, (y - 1) as nat) % z)) % z
{
}

exec fn int_to_bitstring(n: nat) -> (res: Vec<char>)
    ensures
        ValidBitString(res@),
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
            num + Str2Int(result@) * Exp_int(2, result@.len() as nat) == n
    {
        if num % 2nat == 0nat {
            result.push('0');
        } else {
            result.push('1');
        }
        num = num / 2nat;
    }
    
    let mut reversed = Vec::<char>::new();
    let mut i = result.len();
    while i > 0
        invariant
            0 <= i <= result.len(),
            ValidBitString(reversed@),
            reversed@.len() == result.len() - i,
            forall |j: int| 0 <= j && j < reversed@.len() ==> reversed@[j] == result@[result@.len() - 1 - j]
    {
        i = i - 1;
        reversed.push(result[i]);
    }
    
    reversed
}

exec fn modexp_helper(base: nat, exp: nat, modulus: nat) -> (res: nat)
    requires modulus > 1
    ensures res == Exp_int(base, exp) % modulus
    decreases exp
{
    if exp == 0nat {
        proof { lemma_modexp_base(base, modulus); }
        return 1nat % modulus;
    } else {
        proof { lemma_modexp_recursive(base, exp, modulus); }
        let base_mod = base % modulus;
        let rec_result = if exp > 1nat { modexp_helper(base, (exp - 1nat) as nat, modulus) } else { modexp_helper(base, 0nat, modulus) };
        return (base_mod * rec_result) % modulus;
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): converting spec to ghost code for Str2Int calls */
    let ghost x_val = Str2Int(sx@);
    let ghost y_val = Str2Int(sy@);
    let ghost z_val = Str2Int(sz@);
    
    let result_val = modexp_helper(x_val, y_val, z_val);
    let result = int_to_bitstring(result_val);
    
    result
}
// </vc-code>

fn main() {}
}
