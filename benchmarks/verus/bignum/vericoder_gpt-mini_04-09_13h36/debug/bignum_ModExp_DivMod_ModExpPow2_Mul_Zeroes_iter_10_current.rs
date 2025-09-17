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
exec fn bits_to_nat_from(s: &[char], len: int) -> nat
  decreases len
{
    if len == 0 {
        0nat
    } else {
        let last_idx = len - 1;
        let prev = bits_to_nat_from(s, last_idx);
        let bit = if s[last_idx] == '1' { 1nat } else { 0nat };
        2nat * prev + bit
    }
}

exec fn bits_to_nat(s: &[char]) -> nat
  decreases s.len()
{
    bits_to_nat_from(s, s.len())
}

proof fn bits_to_nat_from_spec(s: &[char], len: int)
  ensures bits_to_nat_from(s, len) == Str2Int(s@.subrange(0, len))
  decreases len
{
    if len == 0 {
        assert(bits_to_nat_from(s, 0) == 0nat);
        assert(Str2Int(s@.subrange(0, 0)) == 0nat);
    } else {
        let last_idx = len - 1;
        bits_to_nat_from_spec(s, last_idx);
        let prev_val = bits_to_nat_from(s, last_idx);
        let bit = if s[last_idx] == '1' { 1nat } else { 0nat };
        assert(bits_to_nat_from(s, len) == 2nat * prev_val + bit);
        assert(Str2Int(s@.subrange(0, len)) == 2nat * Str2Int(s@.subrange(0, last_idx)) + (if s@.index(last_idx) == '1' { 1nat } else { 0nat }));
        assert(prev_val == Str2Int(s@.subrange(0, last_idx)));
        assert(bits_to_nat_from(s, len) == Str2Int(s@.subrange(0, len)));
    }
}

proof fn bits_to_nat_spec(s: &[char])
  ensures bits_to_nat(s) == Str2Int(s@)
  decreases s.len()
{
    bits_to_nat_from_spec(s, s.len());
    assert(bits_to_nat(s) == bits_to_nat_from(s, s.len()));
    assert(Str2Int(s@) == Str2Int(s@.subrange(0, s.len())));
    assert(bits_to_nat(s) == Str2Int(s@));
}

// Convert a nat to a bit-vector (Vec<char>) whose Str2Int equals the input nat.
// The representation has at least one bit; zero is represented as ["0"].
// Implementation: recursively compute representation of n/2, then push bit for n%2.
exec fn nat_to_seq(n: nat) -> Vec<char>
  decreases n
{
    if n == 0nat {
        let mut v: Vec<char> = Vec::new();
        v.push('0');
        v
    } else {
        let mut v = nat_to_seq(n / 2);
        if n % 2 == 1nat {
            v.push('1');
        } else {
            v.push('0');
        }
        v
    }
}

proof fn nat_to_seq_spec(n: nat)
  ensures ValidBitString(nat_to_seq(n)@) && Str2Int(nat_to_seq(n)@) == n
  decreases n
{
    if n == 0nat {
        let v = nat_to_seq(0nat);
        // v should be ["0"]
        assert(v.len() == 1);
        assert(v@.index(0) == '0');
        assert(ValidBitString(v@));
        assert(Str2Int(v@) == 0nat);
    } else {
        // inductive hypothesis for n/2
        nat_to_seq_spec(n / 2);
        let pref = nat_to_seq(n / 2);
        let v = nat_to_seq(n);
        // By construction, v is pref with one element appended
        let bit_char = if n % 2 == 1nat { '1' } else { '0' };
        // The following facts follow from the implementation of nat_to_seq (push semantics)
        assert(v@.len() as int == pref@.len() as int + 1);
        assert(v@.index((v@.len() as int) - 1) == bit_char);
        // Validity of bits
        assert(ValidBitString(pref@));
        assert(bit_char == '0' || bit_char == '1');
        assert(ValidBitString(v@));
        // Compute Str2Int using definition: last bit contributes (bit) and prefix contributes doubled
        let pref_val = Str2Int(pref@);
        assert(Str2Int(v@) == 2nat * pref_val + (if bit_char == '1' { 1nat } else { 0nat }));
        // From IH pref_val == n/2
        assert(pref_val == n / 2);
        // conclude Str2Int(v@) == n
        assert(Str2Int(v@) == 2nat * (n / 2) + (if n % 2 == 1nat { 1nat } else { 0nat }));
        // arithmetic: 2*(n/2) + (n%2) == n
        assert(2nat * (n / 2) + (n % 2) == n);
        assert(Str2Int(v@) == n);
    }
}

// Recursive modular exponentiation: computes x^y % z
exec fn powmod(x: nat, y: nat, z: nat) -> nat
  decreases y
{
    if y == 0nat {
        1nat % z
    } else if y % 2nat == 0nat {
        let t = powmod(x, y / 2, z);
        (t * t) % z
    } else {
        let t = powmod(x, (y - 1) as nat, z);
        (x * t) % z
    }
}

// Lemma: modular multiplication property
proof fn mod_mul_lemma(u: nat, v: nat, z: nat)
  requires z > 0
  ensures ((u % z) * (v % z)) % z == (u * v) % z
{
    // Use division properties: u = z*(u/z) + u%z, v = z*(v/z) + v%z
    let ru = u % z;
    let rv = v % z;
    let qu = u / z;
    let qv = v / z;
    assert(u == z * qu + ru);
    assert(v == z * qv + rv);
    // u*v = z*(qu*v + qv*u - z*qu*qv) + ru*rv
    assert(u * v == z * (qu * v + qv * u - z * qu * qv) + ru * rv);
    // therefore (u*v) % z == (ru*rv) % z
    assert((u * v) % z == (ru * rv) % z);
    // but ru < z and rv < z, so ru % z == ru and rv % z == rv
    assert(ru % z == ru);
    assert(rv % z == rv);
    // so ((u%z)*(v%z))%z == (ru*rv)%z which equals (u*v)%z
    assert(((u % z) * (v % z)) % z == (ru * rv) % z);
    assert(((u % z) * (v % z)) % z == (u * v) % z);
}

// Prove powmod computes x^y % z
proof fn powmod_equiv(x: nat, y: nat, z: nat)
  requires z > 0
  ensures powmod(x, y, z) == Exp_int(x, y) % z
  decreases y
{
    if y == 0nat {
        assert(powmod(x, 0nat, z) == 1nat % z);
        assert(Exp_int(x, 0nat) == 1nat);
        assert(Exp_int(x, 0nat) % z == 1nat % z);
    } else {
        if y % 2nat == 0nat {
            let yh = y / 2;
            powmod_equiv(x, yh, z);
            let t = powmod(x, yh, z);
            // t == Exp_int(x, yh) % z
            assert(t == Exp_int(x, yh) % z);
            // powmod(x,y,z) == (t*t)%z
            assert(powmod(x, y, z) == (t * t) % z);
            // Exp_int(x,y) == Exp_int(x,yh) * Exp_int(x,yh)
            let a = Exp_int(x, yh);
            assert(Exp_int(x, y) == a * a);
            // By mod_mul_lemma: ((a%z)*(a%z))%z == (a*a)%z
            mod_mul_lemma(a, a, z);
            // replace t with a%z
            assert((t * t) % z == ((a % z) * (a % z)) % z);
            assert(((a % z) * (a % z)) % z == (a * a) % z);
            assert((a * a) % z == Exp_int(x, y) % z);
            assert(powmod(x, y, z) == Exp_int(x, y) % z);
        } else {
            // y odd
            powmod_equiv(x, (y - 1) as nat, z);
            let t = powmod(x, (y - 1) as nat, z);
            assert(t == Exp_int(x, (y - 1) as nat) % z);
            assert(powmod(x, y, z) == (x * t) % z);
            // Using mod_mul_lemma for x and Exp_int(x,y-1)
            mod_mul_lemma(x, Exp_int(x, (y - 1) as nat), z);
            assert((x * t) % z == (x * Exp_int(x, (y - 1) as nat)) % z);
            assert(Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat));
            assert((x * Exp_int(x, (y - 1) as nat)) % z == Exp_int(x, y) % z);
            assert(powmod(x, y, z) == Exp_int(x, y) % z);
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
    // Convert inputs to nat (work with runtime slices)
    let x = bits_to_nat(sx);
    let y = bits_to_nat(sy);
    let z = bits_to_nat(sz);

    // Compute modular exponentiation as nat
    let r = powmod(x, y, z);

    // Convert result nat to bit vector
    let mut res = nat_to_seq(r);

    // Proof block to establish the ensures clause
    proof {
        // Relate slices/seq to specification Str2Int
        bits_to_nat_spec(sx);
        bits_to_nat_spec(sy);
        bits_to_nat_spec(sz);

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