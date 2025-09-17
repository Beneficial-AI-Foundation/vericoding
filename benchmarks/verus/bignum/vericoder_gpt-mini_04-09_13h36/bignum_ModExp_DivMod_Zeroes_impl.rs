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
exec fn bits_to_nat(s: &[char])
  requires ValidBitString(s@)
  ensures Str2Int(s@) == result
  decreases s.len()
{
    let r: nat = Str2Int(s@);
    r
}

exec fn nat_to_bits(n: nat) -> Vec<char>
  ensures Str2Int(result@) == n && ValidBitString(result@)
  decreases n
{
    if n == 0 {
        let r = Vec::<char>::new();
        proof {
            // Ensure ValidBitString before using Str2Int (recommended)
            assert(ValidBitString(r@));
            assert(Str2Int(r@) == 0);
        }
        r
    } else {
        let prefix = nat_to_bits(n / 2);
        let bit_char = if n % 2 == 1 { '1' } else { '0' };
        let mut res = prefix.clone();
        res.push(bit_char);
        proof {
            // From recursive postcondition
            assert(ValidBitString(prefix@));
            assert(Str2Int(prefix@) == n / 2);

            // res@.subrange(0, len-1) equals prefix@
            assert(res@.subrange(0, res@.len() as int - 1) == prefix@);

            // The last index of res@ is the pushed bit
            let last_idx: int = (res@.len() as int) - 1;
            assert(res@.index(last_idx) == bit_char);

            // Validity of bitstring: combine prefix validity and last bit validity
            assert(ValidBitString(res@));

            // By definition of Str2Int on non-empty sequence:
            assert(Str2Int(res@) == 2 * Str2Int(res@.subrange(0, res@.len() as int - 1)) + (if bit_char == '1' { 1nat } else { 0nat }));

            // Combine with equality of subrange and prefix@
            assert(Str2Int(res@) == 2 * Str2Int(prefix@) + (if bit_char == '1' { 1nat } else { 0nat }));
            assert(Str2Int(res@) == 2 * (n / 2) + (if bit_char == '1' { 1nat } else { 0nat }));

            // Relate bit_char to n % 2
            if n % 2 == 1 {
                assert(bit_char == '1');
                assert((if bit_char == '1' { 1nat } else { 0nat }) == 1nat);
            } else {
                assert(bit_char == '0');
                assert((if bit_char == '1' { 1nat } else { 0nat }) == 0nat);
            }

            // Use division/remainder identity: n == 2*(n/2) + n%2
            assert(2 * (n / 2) + (n % 2) == n);

            // Combine to conclude Str2Int(res@) == n
            assert(Str2Int(res@) == n);
        }
        res
    }
}

proof fn mod_mul_compat(a: nat, b: nat, m: nat)
  requires m > 0
  ensures ((a % m) * b) % m == (a * b) % m
{
    let q = a / m;
    let r = a % m;
    assert(a == q * m + r);
    assert(a * b == q * m * b + r * b);
    // (a * b) % m == (q*m*b + r*b) % m == (r*b) % m
    assert((a * b) % m == (r * b) % m);
    assert((a % m) == r);
    assert(((a % m) * b) % m == (r * b) % m);
    assert(((a % m) * b) % m == (a * b) % m);
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
    let x = bits_to_nat(sx);
    let y = bits_to_nat(sy);
    let z = bits_to_nat(sz);

    // Work modulo z to keep values small; z > 1 by precondition
    let mut pow: nat = 1 % z;
    let mut processed: nat = 0;
    let mut remaining: nat = y;
    // Establish invariants before loop
    proof {
        assert(processed + remaining == y);
        assert(processed == 0);
        assert(pow == 1 % z);
        assert(Exp_int(x, 0) == 1);
        assert(pow == Exp_int(x, processed) % z);
    }
    while remaining > 0
        invariant processed + remaining == y
        invariant pow == Exp_int(x, processed) % z
        decreases remaining
    {
        let prev_processed = processed;
        let prev_pow = pow;
        pow = (prev_pow * x) % z;
        processed = prev_processed + 1;
        remaining = remaining - 1;
        proof {
            // From invariant before the step
            assert(prev_pow == Exp_int(x, prev_processed) % z);

            // pow = (prev_pow * x) % z
            assert(pow == (prev_pow * x) % z);

            // Show pow == Exp_int(x, processed) % z
            // Exp_int(x, prev_processed+1) == Exp_int(x, prev_processed) * x
            assert(Exp_int(x, prev_processed + 1) == Exp_int(x, prev_processed) * x);

            // Use compatibility of multiplication with modulo
            mod_mul_compat(Exp_int(x, prev_processed), x, z);

            // Replace prev_pow with Exp_int(...) % z
            assert((prev_pow * x) % z == (Exp_int(x, prev_processed) * x) % z);

            // Conclude
            assert(pow == Exp_int(x, processed) % z);
        }
    }

    let pow_mod = pow;
    let res = nat_to_bits(pow_mod);
    proof {
        // At loop exit processed == y, so pow == Exp_int(x,y) % z
        assert(processed + remaining == y);
        assert(remaining == 0);
        assert(processed == y);
        assert(pow == Exp_int(x, processed) % z);
        assert(pow == Exp_int(x, y) % z);

        assert(Str2Int(res@) == pow_mod);
        assert(Str2Int(res@) == Exp_int(x, y) % z);
        assert(ValidBitString(res@));
    }
    res
}
// </vc-code>

fn main() {}
}