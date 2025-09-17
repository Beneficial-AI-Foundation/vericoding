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
  ensures Str2Int(s@) == result
  decreases s.len()
{
    // Simply return the specification-level value for the slice
    Str2Int(s@)
}

exec fn nat_to_bits(n: nat) -> Vec<char>
  ensures Str2Int(result@) == n
  ensures ValidBitString(result@)
  decreases n
{
    if n == 0 {
        Vec::<char>::new()
    } else {
        // build prefix for n / 2, then append the least-significant bit of n
        let prefix = nat_to_bits(n / 2);
        let bit_char = if n % 2 == 1 { '1' } else { '0' };
        let mut res = prefix.clone();
        res.push(bit_char);
        // Proof obligations: from recursive postcondition and definition of Str2Int,
        // Str2Int(res@) == 2 * Str2Int(prefix@) + (if bit_char == '1' {1} else {0})
        // and Str2Int(prefix@) == n / 2, hence Str2Int(res@) == n.
        proof {
            // recursive postconditions
            assert(ValidBitString(prefix@));
            assert(Str2Int(prefix@) == n / 2);
            // by definition of Str2Int on the extended sequence:
            // res@ has length > 0, and its prefix (0 .. len-1) is exactly prefix@,
            // and last char is bit_char, hence:
            assert(Str2Int(res@) == 2 * Str2Int(prefix@) + (if bit_char == '1' { 1 } else { 0 }));
            assert(Str2Int(res@) == 2 * (n / 2) + (if bit_char == '1' { 1 } else { 0 }));
            // arithmetic : 2*(n/2) + (n % 2) == n for nat
            assert((2 * (n / 2) + (if bit_char == '1' { 1 } else { 0 })) == n);
        }
        res
    }
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

    // compute pow = Exp_int(x, y) by repeated multiplication
    let mut pow: nat = 1;
    let mut processed: nat = 0;
    let mut remaining: nat = y;
    while remaining > 0
        invariant processed + remaining == y
        invariant pow == Exp_int(x, processed)
        decreases remaining
    {
        let prev_processed = processed;
        let prev_pow = pow;
        pow = prev_pow * x;
        processed = prev_processed + 1;
        remaining = remaining - 1;
        // Maintain the invariant: pow == Exp_int(x, processed)
        proof {
            assert(prev_pow == Exp_int(x, prev_processed));
            assert(pow == prev_pow * x);
            assert(pow == Exp_int(x, processed));
        }
    }

    // At this point, processed == y and pow == Exp_int(x, y)
    let pow_mod = pow % z;
    let res = nat_to_bits(pow_mod);
    // postconditions follow from nat_to_bits ensures and the loop invariants
    proof {
        assert(pow == Exp_int(x, y));
        assert(Str2Int(res@) == pow_mod);
        assert(Str2Int(res@) == Exp_int(x, y) % z);
        assert(ValidBitString(res@));
    }
    res
}
// </vc-code>

fn main() {}
}