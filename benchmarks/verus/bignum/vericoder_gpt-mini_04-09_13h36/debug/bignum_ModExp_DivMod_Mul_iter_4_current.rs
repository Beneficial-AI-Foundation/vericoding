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
// Helper to compute Exp_int as an executable function (iterative version)
exec fn exp_int_exec(x: nat, y: nat) -> nat
  ensures result == Exp_int(x, y)
  decreases y
{
    let mut i: nat = 0;
    let mut acc: nat = 1;

    // Initially acc == Exp_int(x, 0) == 1
    while i < y
      invariant i <= y
      invariant acc == Exp_int(x, i)
      decreases y - i
    {
        let old_i = i;
        let old_acc = acc;
        acc = old_acc * x;
        i = old_i + 1;
        proof {
            // from invariant old_acc == Exp_int(x, old_i)
            assert(old_acc == Exp_int(x, old_i));
            // therefore acc == old_acc * x == Exp_int(x, old_i + 1)
            assert(acc == Exp_int(x, old_i + 1));
        }
    }

    acc
}

// Helper to convert a nat to a Vec<char> bitstring where the last character is the least significant bit.
// Represents 0 as ["0"].
exec fn nat_to_bits(n: nat) -> Vec<char>
  ensures ValidBitString(result@)
  ensures Str2Int(result@) == n
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
        let prefix = nat_to_bits(n / 2);
        let bit = if n % 2 == 1 { '1' } else { '0' };
        let mut v2 = prefix.clone();
        v2.push(bit);
        proof {
            // By recursive postcondition
            assert(Str2Int(prefix@) == n / 2);
            assert(ValidBitString(prefix@));

            // bit value
            let bitval: nat = if bit == '1' { 1 } else { 0 };
            assert(bitval == n % 2);

            // By definition of Str2Int on appended bit:
            assert(Str2Int(v2@) == 2 * Str2Int(prefix@) + bitval);

            // Combine to get Str2Int(v2) == n
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