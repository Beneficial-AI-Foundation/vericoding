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
exec fn bits_to_nat(s: &[char]) -> nat
  decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        let last_idx = s.len() - 1;
        let prev = bits_to_nat(&s[..last_idx]);
        let bit = if s[last_idx] == '1' { 1 } else { 0 };
        2 * prev + bit
    }
}

proof fn bits_to_nat_spec(s: &[char])
  ensures bits_to_nat(s) == Str2Int(s@)
  decreases s.len()
{
    if s.len() == 0 {
        assert(bits_to_nat(s) == 0);
        assert(Str2Int(s@) == 0);
    } else {
        let last_idx = s.len() - 1;
        let prefix = &s[..last_idx];
        bits_to_nat_spec(prefix);
        let bit = if s[last_idx] == '1' { 1 } else { 0 };
        assert(bits_to_nat(s) == 2 * bits_to_nat(prefix) + bit);
        assert(Str2Int(s@) == 2 * Str2Int(prefix@) + bit);
        assert(bits_to_nat(prefix) == Str2Int(prefix@));
        assert(bits_to_nat(s) == Str2Int(s@));
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
    // Convert inputs to nat (work with runtime slices)
    let x = bits_to_nat(sx);
    let y = bits_to_nat(sy);
    let z = bits_to_nat(sz);

    // Compute modular exponentiation as nat
    let r = powmod(x, y, z);

    // Convert result nat to bit vector
    let mut res = nat_to_seq(r);

    // Proof block to establish the ensures clause
    proof {
        // Relate slices/seq to specification Str2Int
        bits_to_nat_spec(sx);
        bits_to_nat_spec(sy);
        bits_to_nat_spec(sz);

        // Relate powmod to spec exponentiation modulo
        powmod_equiv(x, y, z);

        // Relate nat_to_seq result to Str2Int of the resulting Vec
        nat_to_seq_spec(r);

        // Now assemble equalities:
        assert(Str2Int(res@) == r);
        assert(r == powmod(x, y, z));
        assert(powmod(x, y, z) == Exp_int(x, y) % z);
        assert(x == bits_to_nat(sx));
        assert(y == bits_to_nat(sy));
        assert(z == bits_to_nat(sz));
        assert(bits_to_nat(sx) == Str2Int(sx@));
        assert(bits_to_nat(sy) == Str2Int(sy@));
        assert(bits_to_nat(sz) == Str2Int(sz@));
        assert(Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@));
    }

    res
}
// </vc-code>

fn main() {}
}