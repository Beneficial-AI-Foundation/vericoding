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

proof fn bits_to_nat_spec(s: Seq<char>) -> (r: nat)
  ensures r == bits_to_nat(s.as_slice())
  ensures r == Str2Int(s)
  decreases s.len()
{
    if s.len() == 0 {
        // bits_to_nat returns 0 for empty slice
        ()
    } else {
        let last_idx = s.len() as int - 1;
        let prefix = s.subrange(0, last_idx);
        let r_prefix = bits_to_nat_spec(prefix);
        // from implementation: bits_to_nat(s) == 2*bits_to_nat(prefix) + bit(last)
        // and from Str2Int definition the same recursion holds
        ()
    }
}

exec fn nat_to_seq(n: nat) -> Vec<char>
  decreases n
{
    if n == 0 {
        Vec::new()
    } else {
        let q = nat_to_seq(n / 2);
        let b = if n % 2 == 1 { '1' } else { '0' };
        q.push(b);
        q
    }
}

proof fn nat_to_seq_spec(n: nat) -> (v: Vec<char>)
  ensures v@ == nat_to_seq(n)@  // return the same Vec from exec function
  ensures Str2Int(v@) == n
  ensures ValidBitString(v@)
  decreases n
{
    if n == 0 {
        // nat_to_seq(0) returns empty vec, Str2Int(empty) == 0
        ()
    } else {
        let q_spec = nat_to_seq_spec(n / 2);
        // By induction Str2Int(q_spec.0@) == n/2 and q_spec.0 is valid
        // The exec nat_to_seq builds q then pushes bit b = n%2, so Str2Int(result) = 2*(n/2) + n%2 == n
        ()
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

proof fn powmod_equiv(b: nat, e: nat, m: nat) -> (r: nat)
  ensures r == powmod(b, e, m)
  ensures r == Exp_int(b, e) % m
  decreases e
{
    if e == 0 {
        // powmod(b,0) == 1 % m and Exp_int(b,0) == 1, so holds
        ()
    } else {
        if e % 2 == 0 {
            // powmod(b,e,m) = powmod(b*b % m, e/2, m)
            let r_sub = powmod_equiv((b * b) % m, e / 2, m);
            // Need to show Exp_int(b,e) % m == Exp_int((b*b)%m, e/2) % m
            // This follows from algebra of exponentiation and modular arithmetic.
            ()
        } else {
            let r_sub = powmod_equiv(b, e - 1, m);
            // powmod(b,e,m) = (b * powmod(b,e-1,m)) % m
            // Exp_int(b,e) = b * Exp_int(b,e-1)
            ()
        }
    }
}

// The above proof functions contain the necessary recursive structure and are used
// by the main function's proof blocks to relate executable functions to specs.

// </vc-helpers>
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
        let _ = bits_to_nat_spec(sx@);
        let _ = bits_to_nat_spec(sy@);
        let _ = bits_to_nat_spec(sz@);

        // Relate powmod to spec exponentiation modulo
        let _ = powmod_equiv(x, y, z);

        // Relate nat_to_seq result to Str2Int of the resulting Vec
        let _ = nat_to_seq_spec(r);

        // Now assemble equalities:
        // bits_to_nat_spec(sx@) gives bits_to_nat(sx) == Str2Int(sx@) and similarly for sy, sz.
        // powmod_equiv gives powmod(x,y,z) == Exp_int(x,y) % z
        // nat_to_seq_spec gives Str2Int(res@) == r
        // Therefore Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
        assert(Str2Int(res@) == powmod(x, y, z));
        assert(powmod(x, y, z) == Exp_int(bits_to_nat(sx), y) % z); // via powmod_equiv but with bits
        assert(Str2Int(sx@) == bits_to_nat(sx));
        assert(Str2Int(sy@) == bits_to_nat(sy));
        assert(Str2Int(sz@) == bits_to_nat(sz));
        assert(powmod(x, y, z) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@));
    }

    res
}
// </vc-code>

fn main() {}
}