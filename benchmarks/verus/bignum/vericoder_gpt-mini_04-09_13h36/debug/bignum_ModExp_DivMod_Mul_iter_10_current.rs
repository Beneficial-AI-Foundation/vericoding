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
// Helper: convert a bitstring slice to a u64 number (LSB is last char)
exec fn bits_to_u64(s: &[char]) -> u64
  ensures (result as nat) == Str2Int(s@)
{
    let mut acc: u64 = 0;
    let mut i: usize = 0;
    // loop over characters from most-significant (index 0) to least-significant (index len-1)
    while i < s.len()
        invariant i <= s.len();
        invariant (acc as nat) == Str2Int(s@.subrange(0, i as int));
    {
        let c = s[i];
        // compute bit value
        let add: u64 = if c == '1' { 1 } else { 0 };
        let old_acc = acc;
        // update accumulator
        acc = old_acc * 2 + add;
        proof {
            // prove the invariant holds after the step:
            // acc_new as nat == 2 * Str2Int(prefix) + bitval == Str2Int(prefix with new char)
            let prefix = s@.subrange(0, i as int);
            // bit value as nat
            let bitval: nat = if c == '1' { 1 } else { 0 };
            assert((add as nat) == bitval);
            // from old invariant
            assert((old_acc as nat) == Str2Int(prefix));
            // compute new acc as nat
            assert((acc as nat) == 2 * Str2Int(prefix) + bitval);
            // show that equals Str2Int(prefix extended by c)
            assert(Str2Int(s@.subrange(0, (i + 1) as int)) == 2 * Str2Int(prefix) + bitval);
            assert((acc as nat) == Str2Int(s@.subrange(0, (i + 1) as int)));
        }
        i += 1;
    }
    acc
}

// Helper: compute x^y for u64 arguments, with specification relating to Exp_int on nats.
exec fn exp_u64(x: u64, y: u64) -> u64
  ensures (result as nat) == Exp_int((x as nat), (y as nat))
{
    let mut base: u64 = x;
    let mut exp: u64 = y;
    let mut acc: u64 = 1;
    let orig: u64 = y;

    // Loop: multiply acc by base exp times; maintain invariant relating to Exp_int
    while exp > 0
        invariant exp <= orig;
        invariant (acc as nat) * Exp_int((base as nat), (exp as nat)) == Exp_int((x as nat), (orig as nat));
    {
        // perform one multiplication step
        acc = acc * base;
        exp = exp - 1;
    }

    // After loop, exp == 0, so invariant gives acc * Exp_int(base,0) == Exp_int(x,orig)
    // Exp_int(base,0) == 1, so acc == Exp_int(x,orig)
    acc
}

// Lemma: decomposition of n into 2*(n/2) + n%2
proof fn div_mod_decomposition(n: nat)
  decreases n
{
    if n == 0 {
        assert(0 == 2 * (0 / 2) + 0 % 2);
    } else {
        if n % 2 == 0 {
            assert(n == 2 * (n / 2));
            assert(n == 2 * (n / 2) + 0);
        } else {
            assert(n == 2 * (n / 2) + 1);
        }
    }
}

// Helper: convert a u64 natural number to a Vec<char> bitstring (LSB is last char)
// Represents 0 as ["0"]
exec fn nat_to_bits_u64(n: u64) -> Vec<char>
  ensures (ValidBitString(result@) && Str2Int(result@) == (n as nat))
  decreases (n as nat)
{
    if n == 0 {
        let mut v: Vec<char> = Vec::new();
        v.push('0');
        proof {
            assert(ValidBitString(v@));
            assert(Str2Int(v@) == 0);
        }
        v
    } else {
        let pref = nat_to_bits_u64(n / 2);
        let bit = if n % 2 == 1 { '1' } else { '0' };
        let mut v2 = pref.clone();
        v2.push(bit);
        proof {
            // By recursive postcondition
            assert(ValidBitString(pref@));
            assert(Str2Int(pref@) == (n / 2) as nat);

            // bit value
            let bitval: nat = if bit == '1' { 1 } else { 0 };
            assert(bitval == (n % 2) as nat);

            // By definition of Str2Int on appended bit:
            assert(Str2Int(v2@) == 2 * Str2Int(pref@) + bitval);

            // Use lemma about division/remainder decomposition (on nat)
            div_mod_decomposition((n as nat));

            // Combine to get Str2Int(v2) == n
            assert(2 * Str2Int(pref@) + bitval == 2 * ((n / 2) as nat) + (n % 2) as nat);
            assert(2 * ((n / 2) as nat) + (n % 2) as nat == (n as nat));
            assert(Str2Int(v2@) == (n as nat));
            assert(ValidBitString(v2@));
        }
        v2
    }
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
    // Convert input bitstrings to numeric u64 values using helper
    let x_u: u64 = bits_to_u64(sx);
    let y_u: u64 = bits_to_u64(sy);
    let m_u: u64 = bits_to_u64(sz);

    proof {
        // Relate u64 values to spec-level nats
        assert((x_u as nat) == Str2Int(sx@));
        assert((y_u as nat) == Str2Int(sy@));
        assert((m_u as nat) == Str2Int(sz@));
    }

    // Compute full exponent as u64
    let full_exp_u: u64 = exp_u64(x_u, y_u);
    proof {
        // relate to specification Exp_int
        assert((full_exp_u as nat) == Exp_int((x_u as nat), (y_u as nat)));
    }

    // Take modulo m (u64)
    let res_num_u: u64 = full_exp_u % m_u;
    proof {
        // relate to spec-level modulo using casts
        assert((res_num_u as nat) == Exp_int((x_u as nat), (y_u as nat)) % (m_u as nat));
    }

    // Convert numeric result to bitstring Vec<char>
    let res_vec: Vec<char> = nat_to_bits_u64(res_num_u);
    proof {
        // By postcondition of nat_to_bits_u64
        assert(ValidBitString(res_vec@));
        assert(Str2Int(res_vec@) == (res_num_u as nat));
        // Compose equalities to match spec ensures
        assert(Str2Int(res_vec@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@));
    }

    res_vec
}
// </vc-code>

fn main() {}
}