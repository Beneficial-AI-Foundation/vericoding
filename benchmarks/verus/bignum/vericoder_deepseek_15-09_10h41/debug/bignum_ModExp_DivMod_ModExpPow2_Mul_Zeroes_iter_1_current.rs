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

proof fn lemma_exp_int_recursive(x: nat, y: nat)
    requires y > 0
    ensures Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat)
{
    if y > 0 {
        assert(Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat)) by {
            reveal(Exp_int);
        }
    }
}

proof fn lemma_str2int_recursive(s: Seq<char>)
    requires ValidBitString(s), s.len() > 0
    ensures Str2Int(s) == 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat })
{
    if s.len() > 0 {
        assert(Str2Int(s) == 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat })) by {
            reveal(Str2Int);
        }
    }
}

proof fn lemma_exp_mod(x: nat, y: nat, z: nat)
    requires z > 1
    ensures Exp_int(x, y) % z == (x % z) * Exp_int(x, y - 1) % z if y > 0 else 1 % z
{
    if y == 0 {
        assert(Exp_int(x, y) == 1);
        assert(1 % z == 1 % z);
    } else {
        lemma_exp_int_recursive(x, y);
        assert(Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat));
        assert((x * Exp_int(x, (y - 1) as nat)) % z == ((x % z) * (Exp_int(x, (y - 1) as nat) % z)) % z);
    }
}

// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::new();
    let mut base = Str2Int(sx@) % Str2Int(sz@);
    let mut exponent = Str2Int(sy@);
    let modulus = Str2Int(sz@);
    
    result.push('1');
    
    while exponent > 0
        invariant
            ValidBitString(result@),
            Str2Int(result@) == Exp_int(base, exponent) % modulus,
        decreases exponent
    {
        if exponent % 2 == 1 {
            let temp = (Str2Int(result@) * base) % modulus;
            result = int_to_bitstring(temp);
        }
        
        base = (base * base) % modulus;
        exponent = exponent / 2;
    }
    
    result
}
// </vc-code>

fn main() {}
}
