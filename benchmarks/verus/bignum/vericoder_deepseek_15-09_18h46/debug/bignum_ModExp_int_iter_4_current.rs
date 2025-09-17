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
/* helper modified by LLM (iteration 4): remove ghost code from helpers and fix type conversions */
fn nat_from_int(i: int) -> (n: int)
    requires i >= 0
    ensures n == i
{
    i
}

proof fn lemma_nat_arithmetic(a: nat, b: nat)
    requires b > 0
    ensures a % b >= 0 && a % b < b
{
}

proof fn lemma_mod_mul_property(a: nat, b: nat, c: nat)
    requires c > 0
    ensures (a * b) % c == (a % c) * (b % c) % c
{
}

proof fn lemma_pow_mod_property(x: nat, y: nat, z: nat)
    requires z > 1,
    ensures Exp_int(x, y) % z == Exp_int(x % z, y) % z,
    decreases y,
{
    if y > 0 {
        lemma_pow_mod_property(x, (y - 1) as nat, z);
        assert(Exp_int(x, (y - 1) as nat) % z == Exp_int(x % z, (y - 1) as nat) % z);
        assert(Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat));
        assert(Exp_int(x, y) % z == (x * Exp_int(x, (y - 1) as nat)) % z);
        lemma_mod_mul_property(x, Exp_int(x, (y - 1) as nat), z);
        assert((x * Exp_int(x, (y - 1) as nat)) % z == (x % z) * (Exp_int(x, (y - 1) as nat) % z) % z);
        assert(Exp_int(x, y) % z == (x % z) * (Exp_int(x, (y - 1) as nat) % z) % z);
        assert(Exp_int(x, y) % z == (x % z) * (Exp_int(x % z, (y - 1) as nat) % z) % z);
        lemma_mod_mul_property(x % z, Exp_int(x % z, (y - 1) as nat), z);
        assert(Exp_int(x % z, y) % z == (x % z) * Exp_int(x % z, (y - 1) as nat) % z);
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_int(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): fix nat/int type errors by using int arithmetic */
{
    let base_int = Str2Int(sx@) % Str2Int(sz@);
    let mut base = base_int;
    let exponent_int = Str2Int(sy@);
    let mut exponent = exponent_int;
    let modulus = Str2Int(sz@);
    let mut result: int = 1;
    
    while exponent > 0
        invariant
            result >= 0,
            exponent >= 0,
            base >= 0,
            base < modulus,
            modulus > 1,
            Exp_int(Str2Int(sx@), Str2Int(sy@)) % modulus == Exp_int(base as nat, exponent as nat) * result % modulus,
        decreases exponent,
    {
        if exponent % 2 == 1 {
            result = (result * base) % modulus;
        }
        base = (base * base) % modulus;
        exponent = exponent / 2;
    }
    
    let res_chars = if result == 1 { vec!['1'] } else { vec!['0'] };
    res_chars
}
// </vc-code>

fn main() {}
}
