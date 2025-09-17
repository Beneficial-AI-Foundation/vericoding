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
  decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        let prev = bits_to_nat(&s[..s.len() - 1]);
        let bit = if s[s.len() - 1] == '1' { 1 } else { 0 };
        2 * prev + bit
    }
}

proof fn bits_to_nat_spec(s: Seq<char>)
  ensures bits_to_nat(s.as_slice()) == Str2Int(s)
  decreases s.len()
{
    if s.len() == 0 {
        assert(bits_to_nat(s.as_slice()) == 0);
        assert(Str2Int(s) == 0);
    } else {
        let last_idx = s.len() as int - 1;
        let prefix = s.subrange(0, last_idx);
        bits_to_nat_spec(prefix);
        // Relate executable bits_to_nat with specification Str2Int by unfolding definitions
        let bit = if s.index(last_idx) == '1' { 1 } else { 0 };
        assert(bits_to_nat(s.as_slice()) == 2 * bits_to_nat(prefix.as_slice()) + bit);
        assert(Str2Int(s) == 2 * Str2Int(prefix) + bit);
        assert(bits_to_nat(prefix.as_slice()) == Str2Int(prefix));
        assert(bits_to_nat(s.as_slice()) == Str2Int(s));
    }
}

exec fn nat_to_seq(n: nat) -> Vec<char>
  decreases n
{
    if n == 0 {
        Vec::new()
    } else {
        let mut q = nat_to_seq(n / 2);
        let b = if n % 2 == 1 { '1' } else { '0' };
        q.push(b);
        q
    }
}

proof fn nat_to_seq_spec(n: nat)
  ensures Str2Int(nat_to_seq(n)@) == n
  ensures ValidBitString(nat_to_seq(n)@)
  decreases n
{
    if n == 0 {
        assert(nat_to_seq(0)@.len() == 0);
        assert(Str2Int(nat_to_seq(0)@) == 0);
        assert(ValidBitString(nat_to_seq(0)@));
    } else {
        // Induction hypothesis for n/2
        nat_to_seq_spec(n / 2);
        // Let v = nat_to_seq(n) and q = nat_to_seq(n/2)
        let q = nat_to_seq(n / 2);
        let v = nat_to_seq(n);
        let b = if n % 2 == 1 { '1' } else { '0' };
        // By executable function structure, v is q with b appended
        // So Str2Int(v@) == 2 * Str2Int(q@) + (if b == '1' {1} else {0})
        assert(Str2Int(v@) == 2 * Str2Int(q@) + (if b == '1' { 1 } else { 0 }));
        // From IH Str2Int(q@) == n/2
        assert(Str2Int(q@) == n / 2);
        // Validity preserved by push
        assert(ValidBitString(q@));
        assert(ValidBitString(v@));
        // Conclude Str2Int(v@) == n
        assert(Str2Int(v@) == n);
    }
}

exec fn powmod(b: nat, e: nat, m: nat) -> nat
  decreases e
{
    if e == 0 {
        1 % m
    } else {
        if e % 2 == 0 {
            powmod((b * b) % m, e / 2, m)
        } else {
            (b * powmod(b, e - 1, m)) % m
        }
    }
}

proof fn powmod_equiv(b: nat, e: nat, m: nat)
  ensures powmod(b, e, m) == Exp_int(b, e) % m
  decreases e
{
    if e == 0 {
        assert(powmod(b, 0, m) == 1 % m);
        assert(Exp_int(b, 0) == 1);
        assert(powmod(b, 0, m) == Exp_int(b, 0) % m);
    } else {
        if e % 2 == 0 {
            // even case
            powmod_equiv((b * b) % m, e / 2, m);
            // powmod(b,e,m) = powmod((b*b)%m, e/2, m)
            assert(powmod(b, e, m) == powmod((b * b) % m, e / 2, m));
            // by IH powmod((b*b)%m, e/2, m) == Exp_int((b*b)%m, e/2) % m
            assert(powmod((b * b) % m, e / 2, m) == Exp_int((b * b) % m, e / 2) % m);
            // Now show Exp_int(b,e) % m == Exp_int((b*b)%m, e/2) % m
            // Exp_int(b, e) = Exp_int(b, e/2) * Exp_int(b, e/2)
            assert(Exp_int(b, e) == Exp_int(b, e / 2) * Exp_int(b, e / 2));
            // Reduce modulo: (a*b) % m == ((a % m) * (b % m)) % m
            assert(Exp_int(b, e) % m == (Exp_int(b, e / 2) % m) * (Exp_int(b, e / 2) % m) % m);
            // Note that Exp_int((b*b)%m, e/2) % m == (Exp_int(b, e/2) % m) * (Exp_int(b, e/2) % m) % m
            // So they are equal, hence powmod(b,e,m) == Exp_int(b,e) % m
            assert(powmod(b, e, m) == Exp_int(b, e) % m);
        } else {
            // odd case
            powmod_equiv(b, e - 1, m);
            assert(powmod(b, e, m) == (b * powmod(b, e - 1, m)) % m);
            assert(powmod(b, e - 1, m) == Exp_int(b, e - 1) % m);
            // (b * (Exp_int(b,e-1) % m)) % m == (b * Exp_int(b,e-1)) % m == Exp_int(b,e) % m
            assert((b * (Exp_int(b, e - 1) % m)) % m == (b * Exp_int(b, e - 1)) % m);
            assert((b * Exp_int(b, e - 1)) % m == Exp_int(b, e) % m);
            assert(powmod(b, e, m) == Exp_int(b, e) % m);
        }
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2_Mul_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    // Convert inputs to nat
    let x = bits_to_nat(sx);
    let y = bits_to_nat(sy);
    let z = bits_to_nat(sz);

    // Compute modular exponentiation as nat
    let r = powmod(x, y, z);

    // Convert result nat to bit vector
    let mut res = nat_to_seq(r);

    // Proof block to establish the ensures clause
    proof {
        // Relate slices to specification Str2Int
        bits_to_nat_spec(sx@);
        bits_to_nat_spec(sy@);
        bits_to_nat_spec(sz@);

        // Relate powmod to spec exponentiation modulo
        powmod_equiv(x, y, z);

        // Relate nat_to_seq result to Str2Int of the resulting Vec
        nat_to_seq_spec(r);

        // Now assemble equalities:
        assert(Str2Int(res@) == r);
        assert(r == powmod(x, y, z));
        assert(powmod(x, y, z) == Exp_int(x, y) % z);
        assert(x == bits_to_nat(sx));
        assert(y == bits_to_nat(sy));
        assert(z == bits_to_nat(sz));
        assert(bits_to_nat(sx) == Str2Int(sx@));
        assert(bits_to_nat(sy) == Str2Int(sy@));
        assert(bits_to_nat(sz) == Str2Int(sz@));
        assert(Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@));
    }

    res
}
// </vc-code>

fn main() {}
}