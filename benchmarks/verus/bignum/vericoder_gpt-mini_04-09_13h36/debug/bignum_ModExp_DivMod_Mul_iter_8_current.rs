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
// Helper to compute Exp_int as an executable function (recursive version)
exec fn exp_int_exec(x: nat, y: nat) -> nat
  ensures result == Exp_int(x, y)
  decreases y
{
    if y == 0 {
        1
    } else {
        let t = exp_int_exec(x, (y - 1) as nat);
        // match the specification Exp_int(x,y) = if y==0 {1} else { x * Exp_int(x, y-1) }
        x * t
    }
}

// Lemma: decomposition of n into 2*(n/2) + n%2
proof fn div_mod_decomposition(n: nat)
  decreases n
{
    if n == 0 {
        // 0 == 2*(0/2) + 0%2 holds trivially
        assert(0 == 2 * (0 / 2) + 0 % 2);
    } else {
        if n % 2 == 0 {
            // n even: n == 2*(n/2)
            assert(n == 2 * (n / 2));
            assert(n == 2 * (n / 2) + 0);
        } else {
            // n odd: n == 2*(n/2) + 1
            assert(n == 2 * (n / 2) + 1);
        }
    }
}

// Helper to convert a nat to a Vec<char> bitstring where the last character is the least significant bit.
// Represents 0 as ["0"].
exec fn nat_to_bits(n: nat) -> Vec<char>
  ensures (ValidBitString(result@) && Str2Int(result@) == n)
  decreases n
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
        // recursive call on n/2 (which is < n for n > 0)
        let pref = nat_to_bits(n / 2);
        let bit = if n % 2 == 1 { '1' } else { '0' };
        let mut v2 = pref.clone();
        v2.push(bit);
        proof {
            // By recursive postcondition
            assert(Str2Int(pref@) == n / 2);
            assert(ValidBitString(pref@));

            // bit value
            let bitval: nat = if bit == '1' { 1 } else { 0 };
            assert(bitval == n % 2);

            // By definition of Str2Int on appended bit:
            assert(Str2Int(v2@) == 2 * Str2Int(pref@) + bitval);

            // Use lemma about division/remainder decomposition
            div_mod_decomposition(n);

            // Combine to get Str2Int(v2) == n
            assert(2 * Str2Int(pref@) + bitval == 2 * (n / 2) + n % 2);
            assert(2 * (n / 2) + n % 2 == n);
            assert(Str2Int(v2@) == n);
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
    // Compute numeric values
    let x: nat = Str2Int(sx@);
    let y: nat = Str2Int(sy@);
    let m: nat = Str2Int(sz@);

    // Compute full exponent Exp_int(x, y) using executable version, then take modulo m
    let full_exp: nat = exp_int_exec(x, y);
    proof {
        assert(full_exp == Exp_int(x, y));
    }
    let res_num: nat = full_exp % m;
    proof {
        assert(res_num == Exp_int(x, y) % m);
    }

    // Convert result number to bitstring representation
    let res_vec: Vec<char> = nat_to_bits(res_num);
    proof {
        assert(Str2Int(res_vec@) == res_num);
        assert(ValidBitString(res_vec@));
        assert(Str2Int(res_vec@) == Exp_int(x, y) % m);
    }

    // Return the bitstring
    res_vec
}
// </vc-code>

fn main() {}
}