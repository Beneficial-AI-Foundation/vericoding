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
exec fn bits_to_nat(s: Seq<char>) -> nat
  decreases s.len()
{
    if s.len() as int == 0 {
        0
    } else {
        let last_idx = s.len() as int - 1;
        let prev = bits_to_nat(s.subrange(0, last_idx));
        let bit = if s.index(last_idx) == '1' { 1 } else { 0 };
        2 * prev + bit
    }
}

proof fn bits_to_nat_spec(s: Seq<char>)
  ensures bits_to_nat(s) == Str2Int(s)
  decreases s.len()
{
    if s.len() as int == 0 {
        assert(bits_to_nat(s) == 0);
        assert(Str2Int(s) == 0);
    } else {
        let last_idx = s.len() as int - 1;
        let prefix = s.subrange(0, last_idx);
        bits_to_nat_spec(prefix);
        let bit = if s.index(last_idx) == '1' { 1 } else { 0 };
        assert(bits_to_nat(s) == 2 * bits_to_nat(prefix) + bit);
        assert(Str2Int(s) == 2 * Str2Int(prefix) + bit);
        assert(bits_to_nat(prefix) == Str2Int(prefix));
        assert(bits_to_nat(s) == Str2Int(s));
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
  ensures Str2Int(nat_to_seq(n)@) == n && ValidBitString(nat_to_seq(n)@)
  decreases n
{
    if n == 0 {
        assert(nat_to_seq(0)@.len() == 0);
        assert(Str2Int(nat_to_seq(0)@) == 0);
        assert(ValidBitString(nat_to_seq(0)@));
    } else {
        nat_to_seq_spec(n / 2);
        let q = nat_to_seq(n / 2);
        let v = nat_to_seq(n);
        let b = if n % 2 == 1 { '1' } else { '0' };

        assert(Str2Int(q@) == n / 2);
        assert(ValidBitString(q@));

        // v is q with b appended by construction of nat_to_seq
        assert(Str2Int(v@) == 2 * Str2Int(q@) + (if b == '1' { 1 } else { 0 }));

        assert(Str2Int(v@) == 2 * (n / 2) + (if b == '1' { 1 } else { 0 }));
        assert((if b == '1' { 1 } else { 0 }) == (n % 2));
        assert(2 * (n / 2) + (n % 2) == n);
        assert(Str2Int(v@) == n);

        assert(b == '0' || b == '1');
        assert(ValidBitString(v@));
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

proof fn Exp_int_add(b: nat, n: nat, m: nat)
  ensures Exp_int(b, n + m) == Exp_int(b, n) * Exp_int(b, m)
  decreases m
{
    if m == 0 {
        assert(Exp_int(b, n + 0) == Exp_int(b, n));
        assert(Exp_int(b, n) * Exp_int(b, 0) == Exp_int(b, n) * 1);
        assert(Exp_int(b, n + m) == Exp_int(b, n) * Exp_int(b, m));
    } else {
        Exp_int_add(b, n, m - 1);
        assert(Exp_int(b, n + m) == b * Exp_int(b, n + m - 1));
        assert(Exp_int(b, n) * Exp_int(b, m) == b * (Exp_int(b, n) * Exp_int(b, m - 1)));
        assert(Exp_int(b, n + m - 1) == Exp_int(b, n) * Exp_int(b, m - 1));
        assert(Exp_int(b, n + m) == Exp_int(b, n) * Exp_int(b, m));
    }
}

proof fn div_even_double(e: nat)
  requires e % 2 == 0
  ensures e == (e / 2) + (e / 2)
  decreases e
{
    let k = e / 2;
    assert(e == 2 * k + e % 2);
    assert(e % 2 == 0);
    assert(e == 2 * k);
    assert(e == k + k);
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
            powmod_equiv((b * b) % m, e / 2, m);
            assert(powmod(b, e, m) == powmod((b * b) % m, e / 2, m));
            assert(powmod((b * b) % m, e / 2, m) == Exp_int((b * b) % m, e / 2) % m);

            div_even_double(e);
            let k = e / 2;
            Exp_int_add(b, k, k);
            assert(Exp_int(b, e) == Exp_int(b, k) * Exp_int(b, k));

            assert((Exp_int(b, k) * Exp_int(b, k)) % m == Exp_int(b, e) % m);

            assert(Exp_int((b * b) % m, k) % m == (Exp_int(b, k) * Exp_int(b, k)) % m);

            assert(Exp_int(b, e) % m == Exp_int((b * b) % m, k) % m);
            assert(powmod(b, e, m) == Exp_int(b, e) % m);
        } else {
            powmod_equiv(b, e - 1, m);
            assert(powmod(b, e, m) == (b * powmod(b, e - 1, m)) % m);
            assert(powmod(b, e - 1, m) == Exp_int(b, e - 1) % m);
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
    // Convert inputs to nat (convert slices to Seq with @)
    let x = bits_to_nat(sx@);
    let y = bits_to_nat(sy@);
    let z = bits_to_nat(sz@);

    // Compute modular exponentiation as nat
    let r = powmod(x, y, z);

    // Convert result nat to bit vector
    let mut res = nat_to_seq(r);

    // Proof block to establish the ensures clause
    proof {
        // Relate slices/seq to specification Str2Int
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
        assert(x == bits_to_nat(sx@));
        assert(y == bits_to_nat(sy@));
        assert(z == bits_to_nat(sz@));
        assert(bits_to_nat(sx@) == Str2Int(sx@));
        assert(bits_to_nat(sy@) == Str2Int(sy@));
        assert(bits_to_nat(sz@) == Str2Int(sz@));
        assert(Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@));
    }

    res
}
// </vc-code>

fn main() {}
}