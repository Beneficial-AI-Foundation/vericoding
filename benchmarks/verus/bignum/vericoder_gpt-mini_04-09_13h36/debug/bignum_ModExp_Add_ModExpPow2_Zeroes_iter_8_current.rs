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
        return 0nat;
    } else {
        let len = s.len();
        let last = s[len - 1];
        let prev = seq_to_nat(&s[..len - 1]);
        if last == '1' {
            return 2nat * prev + 1nat;
        } else {
            return 2nat * prev;
        }
    }
}

proof fn div_mod_two(n: nat)
  ensures 2nat * (n / 2nat) + (n % 2nat) == n
  decreases n
{
    if n == 0nat {
        // trivial
    } else {
        if n % 2nat == 0nat {
            // n is even, so remainder 0 and n == 2*(n/2)
            assert(2nat * (n / 2nat) + (n % 2nat) == 2nat * (n / 2nat) + 0nat);
            assert(2nat * (n / 2nat) + 0nat == n);
        } else {
            // n is odd, remainder 1 and n == 2*(n/2) + 1
            assert(n % 2nat == 1nat);
            assert(2nat * (n / 2nat) + (n % 2nat) == 2nat * (n / 2nat) + 1nat);
            assert(2nat * (n / 2nat) + 1nat == n);
        }
    }
}

proof fn lemma_Exp_add(base: nat, a: nat, b: nat)
  ensures Exp_int(base, a + b) == Exp_int(base, a) * Exp_int(base, b)
  decreases b
{
    if b == 0nat {
        assert(Exp_int(base, a + 0nat) == Exp_int(base, a));
        assert(Exp_int(base, 0nat) == 1nat);
        assert(Exp_int(base, a) == Exp_int(base, a) * Exp_int(base, 0nat));
    } else {
        lemma_Exp_add(base, a, b - 1nat);
        assert(Exp_int(base, a + b) == base * Exp_int(base, a + b - 1nat));
        assert(Exp_int(base, b) == base * Exp_int(base, b - 1nat));
        assert(Exp_int(base, a + b - 1nat) == Exp_int(base, a) * Exp_int(base, b - 1nat));
        assert(base * Exp_int(base, a + b - 1nat) == Exp_int(base, a) * (base * Exp_int(base, b - 1nat)));
        assert(base * Exp_int(base, a + b - 1nat) == Exp_int(base, a) * Exp_int(base, b));
        assert(Exp_int(base, a + b) == Exp_int(base, a) * Exp_int(base, b));
    }
}

exec fn nat_to_bits(n: nat) -> (res: Vec<char>)
  ensures Str2Int(res@) == n
  ensures ValidBitString(res@)
  decreases n
{
    if n == 0nat {
        return Vec::<char>::new();
    } else {
        let q: nat = n / 2nat;
        let bit_char: char = if n % 2nat == 1nat { '1' } else { '0' };
        let mut v = nat_to_bits(q);
        let prev_seq = v@; // snapshot before push
        v.push(bit_char);
        proof {
            assert(Str2Int(prev_seq) == q);
            assert(ValidBitString(prev_seq));
            let L: int = v@.len() as int;
            assert(L >= 1);
            assert(Str2Int(v@) == 2nat * Str2Int(v@.subrange(0, L - 1)) + (if v@.index(L - 1) == '1' { 1nat } else { 0nat }));
            assert(v@.subrange(0, L - 1) == prev_seq);
            assert(v@.index(L - 1) == bit_char);
            assert(Str2Int(v@) == 2nat * q + (if bit_char == '1' { 1nat } else { 0nat }));
            assert((if bit_char == '1' { 1nat } else { 0nat }) == (n % 2nat));
            assert(Str2Int(v@) == 2nat * q + (n % 2nat));
            div_mod_two(n);
            assert(2nat * q + (n % 2nat) == n);
            assert(Str2Int(v@) == n);
            assert(ValidBitString(v@));
        }
        return v;
    }
}

exec fn pow_mod(base: nat, exp: nat, modulus: nat) -> (res: nat)
  requires modulus > 0
  ensures res == Exp_int(base, exp) % modulus
  decreases exp
{
    if exp == 0nat {
        return 1nat % modulus;
    } else if exp % 2nat == 0nat {
        let t = pow_mod(base, exp / 2nat, modulus);
        let r = (t * t) % modulus;
        proof {
            assert(t == Exp_int(base, exp / 2nat) % modulus);
            div_mod_two(exp);
            assert(2nat * (exp / 2nat) + (exp % 2nat) == exp);
            assert(exp % 2nat == 0nat);
            assert(2nat * (exp / 2nat) == exp);
            lemma_Exp_add(base, exp / 2nat, exp / 2nat);
            assert(Exp_int(base, exp) == Exp_int(base, exp / 2nat) * Exp_int(base, exp / 2nat));
            assert(r == Exp_int(base, exp) % modulus);
        }
        return r;
    } else {
        let t = pow_mod(base, exp - 1nat, modulus);
        let r = ((base % modulus) * t) % modulus;
        proof {
            assert(t == Exp_int(base, exp - 1nat) % modulus);
            assert(Exp_int(base, exp) == base * Exp_int(base, exp - 1nat));
            assert(r == Exp_int(base, exp) % modulus);
        }
        return r;
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