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
            // By induction hypothesis
            assert(Str2Int(prev_seq) == q);
            assert(ValidBitString(prev_seq));
            // Now v@ is prev_seq ++ [bit_char]
            let L: int = v@.len() as int;
            // L >= 1 because we pushed
            assert(L >= 1);
            // Use definition of Str2Int for non-empty sequences
            assert(Str2Int(v@) == 2nat * Str2Int(v@.subrange(0, L - 1)) + (if v@.index(L - 1) == '1' { 1nat } else { 0nat }));
            // The prefix equals prev_seq
            assert(v@.subrange(0, L - 1) == prev_seq);
            // The last char equals bit_char
            assert(v@.index(L - 1) == bit_char);
            // Combine to get Str2Int(v@) == 2*q + (n % 2)
            assert(Str2Int(v@) == 2nat * q + (if bit_char == '1' { 1nat } else { 0nat }));
            // arithmetic equality: 2*q + (n % 2) == n
            assert(2nat * q + (n % 2nat) == n);
            assert(Str2Int(v@) == n);
            // ValidBitString: prefix valid and last is '0' or '1'
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
            // t == Exp_int(base, exp/2) % modulus
            assert(t == Exp_int(base, exp / 2nat) % modulus);
            // Exp_int(base, exp) == Exp_int(base, exp/2) * Exp_int(base, exp/2)
            assert(Exp_int(base, exp) == Exp_int(base, exp / 2nat) * Exp_int(base, exp / 2nat));
            // r equals the product modulo modulus, so equals Exp_int(base, exp) % modulus
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

    // Provide an explicit proof that the result satisfies the spec ensures
    proof {
        // seq_to_nat ensures correspondence with Str2Int
        assert(x == Str2Int(sx@));
        assert(y == Str2Int(sy@));
        assert(z == Str2Int(sz@));

        // pow_mod ensures r_nat equals Exp_int(x,y) % z
        assert(r_nat == Exp_int(x, y) % z);

        // nat_to_bits ensures Str2Int(res_vec@) == r_nat and ValidBitString
        assert(Str2Int(res_vec@) == r_nat);
        assert(ValidBitString(res_vec@));

        // Combine equalities to match the specification
        assert(Str2Int(res_vec@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@));
        assert(ValidBitString(res_vec@));
    }

    res_vec
}
// </vc-code>

fn main() {}
}