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
// Helper to compute Exp_int as an executable function
exec fn exp_int_exec(x: nat, y: nat) -> nat
  decreases y
  ensures result == Exp_int(x, y)
{
    if y == 0 {
        1
    } else {
        let t = exp_int_exec(x, y - 1);
        let r = x * t;
        proof {
            // by induction hypothesis t == Exp_int(x, y-1)
            assert(t == Exp_int(x, y - 1));
            // hence r == x * Exp_int(x, y-1) == Exp_int(x, y)
            assert(r == Exp_int(x, y));
        }
        r
    }
}

// Helper to convert a nat to a Vec<char> bitstring where the last character is the least significant bit.
// Represents 0 as ["0"].
exec fn nat_to_bits(n: nat) -> Vec<char>
  decreases n
  ensures ValidBitString(result@)
  ensures Str2Int(result@) == n
{
    if n == 0 {
        let mut v: Vec<char> = Vec::new();
        v.push('0');
        proof {
            // v@ is a sequence of length 1 with character '0'
            assert(ValidBitString(v@));
            // Str2Int(['0']) = 2 * Str2Int([]) + 0 = 0
            assert(Str2Int(v@) == 0);
        }
        v
    } else {
        let prefix = nat_to_bits(n / 2);
        let bit = if n % 2 == 1 { '1' } else { '0' };
        let mut v2 = prefix.clone();
        v2.push(bit);
        proof {
            // prefix satisfies Str2Int(prefix) == n/2 by recursion
            assert(Str2Int(prefix@) == n / 2);
            assert(ValidBitString(prefix@));

            // bit value as nat
            let bitval: nat = if bit == '1' { 1 } else { 0 };
            assert(bitval == n % 2);

            // By definition of Str2Int on a sequence whose last element is bit:
            // Str2Int(prefix ++ [bit]) = 2 * Str2Int(prefix) + bitval
            assert(Str2Int(v2@) == 2 * Str2Int(prefix@) + bitval);

            // Combine to get Str2Int(v2) == 2*(n/2) + (n%2) == n
            assert(2 * Str2Int(prefix@) + bitval == n);
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
    let res_num: nat = full_exp % m;

    // Convert result number to bitstring representation
    let res_vec: Vec<char> = nat_to_bits(res_num);

    // Return the bitstring
    res_vec
}
// </vc-code>

fn main() {}
}