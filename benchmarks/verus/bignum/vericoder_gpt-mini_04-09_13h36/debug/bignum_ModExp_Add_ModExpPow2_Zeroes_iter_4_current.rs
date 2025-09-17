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
        0
    } else {
        let len = s.len();
        let last = s[len - 1];
        let prev = seq_to_nat(&s[..len - 1]);
        if last == '1' {
            2 * prev + 1
        } else {
            2 * prev
        }
    }
}

exec fn nat_to_bits(n: nat) -> (res: Vec<char>)
  ensures Str2Int(res@) == n
  decreases n
{
    if n == 0 {
        Vec::<char>::new()
    } else {
        let q: nat = n / 2;
        let bit_char: char = if n % 2 == 1 { '1' } else { '0' };
        let mut v = nat_to_bits(q);
        let prev_seq = v@; // snapshot before push
        v.push(bit_char);
        proof {
            // By induction, Str2Int(prev_seq) == q
            assert(Str2Int(prev_seq) == q);
            // Now v@ is prev_seq concatenated with [bit_char].
            let L: int = v@.len() as int;
            assert(L >= 1);
            // Using the definition of Str2Int for non-empty sequences:
            assert(Str2Int(v@) == 2 * Str2Int(v@.subrange(0, L - 1)) + (if v@.index(L - 1) == '1' { 1 } else { 0 }));
            // v@.subrange(0, L-1) == prev_seq
            assert(v@.subrange(0, L - 1) == prev_seq);
            // last char equals bit_char
            assert(v@.index(L - 1) == bit_char);
            // combine equalities to get Str2Int(v@) == 2*q + (n%2)
            assert(Str2Int(v@) == 2 * q + (if bit_char == '1' { 1 } else { 0 }));
            // arithmetic: 2*q + (n%2) == n
            assert(2 * q + (n % 2) == n);
            // conclude
            assert(Str2Int(v@) == n);
        }
        v
    }
}

exec fn pow_mod(base: nat, exp: nat, modulus: nat) -> (res: nat)
  requires modulus > 0
  ensures res == Exp_int(base, exp) % modulus
  decreases exp
{
    if exp == 0 {
        1 % modulus
    } else if exp % 2 == 0 {
        let t = pow_mod(base, exp / 2, modulus);
        let r = (t * t) % modulus;
        proof {
            assert(t == Exp_int(base, exp / 2) % modulus);
            assert(Exp_int(base, exp) == Exp_int(base, exp / 2) * Exp_int(base, exp / 2));
            assert(r == Exp_int(base, exp) % modulus);
        }
        r
    } else {
        let t = pow_mod(base, exp - 1, modulus);
        let r = ((base % modulus) * t) % modulus;
        proof {
            assert(t == Exp_int(base, exp - 1) % modulus);
            assert(Exp_int(base, exp) == base * Exp_int(base, exp - 1));
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