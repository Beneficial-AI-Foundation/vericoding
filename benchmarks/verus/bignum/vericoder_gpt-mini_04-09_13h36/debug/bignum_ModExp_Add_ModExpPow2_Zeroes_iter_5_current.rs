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
exec fn seq_to_nat(s: &[char]) -> (res: nat)
  requires ValidBitString(s@)
  ensures res == Str2Int(s@)
  decreases s.len()
{
    if s.len() == 0 {
        0nat
    } else {
        let len = s.len();
        let last = s[len - 1];
        let prev = seq_to_nat(&s[..len - 1]);
        if last == '1' {
            2nat * prev + 1nat
        } else {
            2nat * prev
        }
    }
}

exec fn nat_to_bits(n: nat) -> (res: Vec<char>)
  ensures Str2Int(res@) == n
  ensures ValidBitString(res@)
  decreases n
{
    if n == 0nat {
        Vec::<char>::new()
    } else {
        let q: nat = n / 2nat;
        let bit_char: char = if n % 2nat == 1nat { '1' } else { '0' };
        let mut v = nat_to_bits(q);
        let prev_seq = v@; // snapshot before push
        v.push(bit_char);
        proof {
            // By induction, Str2Int(prev_seq) == q and ValidBitString(prev_seq)
            assert(Str2Int(prev_seq) == q);
            assert(ValidBitString(prev_seq));
            // Now v@ is prev_seq concatenated with [bit_char].
            let L: int = v@.len() as int;
            assert(L >= 1);
            // Using the definition of Str2Int for non-empty sequences:
            assert(Str2Int(v@) == 2nat * Str2Int(v@.subrange(0, L - 1)) + (if v@.index(L - 1) == '1' { 1nat } else { 0nat }));
            // v@.subrange(0, L-1) == prev_seq
            assert(v@.subrange(0, L - 1) == prev_seq);
            // last char equals bit_char
            assert(v@.index(L - 1) == bit_char);
            // combine equalities to get Str2Int(v@) == 2*q + (n%2)
            assert(Str2Int(v@) == 2nat * q + (if bit_char == '1' { 1nat } else { 0nat }));
            // arithmetic: 2*q + (n%2) == n
            assert(2nat * q + (n % 2nat) == n);
            // conclude
            assert(Str2Int(v@) == n);
            // prove ValidBitString for v@
            // all indices i < L-1 are from prev_seq which is valid,
            // and index L-1 is either '0' or '1' (bit_char).
            assert(ValidBitString(v@));
        }
        v
    }
}

exec fn pow_mod(base: nat, exp: nat, modulus: nat) -> (res: nat)
  requires modulus > 0
  ensures res == Exp_int(base, exp) % modulus
  decreases exp
{
    if exp == 0nat {
        1nat % modulus
    } else if exp % 2nat == 0nat {
        let t = pow_mod(base, exp / 2nat, modulus);
        let r = (t * t) % modulus;
        proof {
            assert(t == Exp_int(base, exp / 2nat) % modulus);
            assert(Exp_int(base, exp) == Exp_int(base, exp / 2nat) * Exp_int(base, exp / 2nat));
            assert(r == Exp_int(base, exp) % modulus);
        }
        r
    } else {
        let t = pow_mod(base, exp - 1nat, modulus);
        let r = ((base % modulus) * t) % modulus;
        proof {
            assert(t == Exp_int(base, exp - 1nat) % modulus);
            assert(Exp_int(base, exp) == base * Exp_int(base, exp - 1nat));
            assert(r == Exp_int(base, exp) % modulus);
        }
        r
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    // Convert inputs to natural numbers
    let x: nat = seq_to_nat(sx);
    let y: nat = seq_to_nat(sy);
    let z: nat = seq_to_nat(sz);

    // modulus z > 1 given by precondition, so z > 0 holds
    let r_nat: nat = pow_mod(x, y, z);

    // Convert result to bit-vector
    let res_vec: Vec<char> = nat_to_bits(r_nat);

    res_vec
}
// </vc-code>

fn main() {}
}