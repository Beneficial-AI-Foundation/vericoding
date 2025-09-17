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
exec fn slice_to_nat(s: &[char]) -> nat
  requires ValidBitString(s@)
  ensures result == Str2Int(s@)
  decreases s.len()
{
    if s.len() == 0 {
        return 0;
    } else {
        let n = s.len();
        let prefix = &s[..n-1];
        let q = slice_to_nat(prefix);
        if s[n-1] == '1' {
            return 2 * q + 1;
        } else {
            return 2 * q;
        }
    }
}

exec fn nat_to_vec(n: nat) -> Vec<char>
  ensures ValidBitString(result@) && Str2Int(result@) == n
  decreases n
{
    if n == 0 {
        return Vec::new();
    } else {
        let q = n / 2;
        let bit = if n % 2 == 1 { '1' } else { '0' };
        let mut v = nat_to_vec(q);
        let old = v@;
        v.push(bit);
        proof {
            // Validity of bits preserved
            assert(ValidBitString(old));
            assert(bit == '0' || bit == '1');
            assert(ValidBitString(v@));

            // lengths and content relations after push
            assert(v@.len() as int == old.len() as int + 1);
            assert(v@.subrange(0, (v@.len() as int - 1)) == old);
            assert(v@.index(v@.len() as int - 1) == bit);

            // Str2Int unfolding for non-empty sequence
            assert(v@.len() > 0);
            // By definition of Str2Int on non-empty sequences
            assert(Str2Int(v@) == 2 * Str2Int(v@.subrange(0, v@.len() as int - 1)) + (if v@.index(v@.len() as int - 1) == '1' { 1 } else { 0 }));

            // Substitute known equalities
            assert(Str2Int(v@.subrange(0, v@.len() as int - 1)) == Str2Int(old));
            assert(Str2Int(old) == q);
            assert((if bit == '1' { 1 } else { 0 }) == n % 2);
            assert(2 * q + n % 2 == n);
            assert(Str2Int(v@) == n);
        }
        return v;
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Add_Zeroes_DivMod_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    // Compute numeric values of base and modulus
    let base = slice_to_nat(sx);
    let modulus = slice_to_nat(sz);

    // Precondition ensures modulus > 1
    // Prepare reduced base mod modulus
    let xmod = base % modulus;

    // Initialize result as 1 (Exp_int(base,0) == 1)
    let mut r: nat = 1 % modulus;

    // Iterate bits of exponent sy from MSB (index 0) to LSB (index len-1)
    let mut i: usize = 0usize;
    while i < sy.len()
        invariant i <= sy.len()
        invariant r < modulus
        invariant r == Exp_int(base, Str2Int(sy@.subrange(0, i as int))) % modulus
        decreases sy.len() - i
    {
        // square
        r = (r * r) % modulus;

        // multiply by base if current bit is '1'
        if sy[i] == '1' {
            r = (r * xmod) % modulus;
        }

        i = i + 1;
    }

    // Convert numeric result r into bit vector
    let res = nat_to_vec(r);
    return res;
}
// </vc-code>

fn main() {}
}