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
// Helper functions and proofs for ModExp_int

exec fn slice_to_nat(s: &[char]) -> nat
  requires ValidBitString(s@)
  ensures result == Str2Int(s@)
  decreases s@.len()
{
    if s@.len() == 0 {
        0
    } else {
        let len: nat = s@.len();
        let last_idx: usize = (len - 1) as usize;
        let last_c: char = s[last_idx];
        let rest: &[char] = &s[..last_idx];
        let r: nat = slice_to_nat(rest);
        if last_c == '1' {
            r * 2 + 1
        } else {
            r * 2
        }
    }
}

proof fn lemma_div_mod_2(m: nat)
  ensures m == 2*(m/2) + (m % 2)
{
    // Directly assert the standard division-remainder identity for divisor 2.
    assert(m == 2*(m/2) + (m % 2));
}

proof fn lemma_div_mod(x: nat, m: nat)
  requires m > 0
  ensures x == m*(x/m) + (x % m)
{
    // Standard division-remainder identity for general m > 0
    assert(x == m*(x/m) + (x % m));
}

proof fn lemma_mod_mul(m: nat, x: nat, y: nat)
  requires m > 0
  ensures ((x % m) * y) % m == (x * y) % m
{
    // Use division identity to rewrite x and multiply by y
    lemma_div_mod(x, m);
    assert(x == m*(x/m) + x % m);
    assert(x * y == m*(x/m)*y + (x % m) * y);
    // therefore x*y and (x%m)*y differ by a multiple of m, so have same remainder mod m
    assert((x * y) % m == ((x % m) * y) % m);
}

exec fn nat_to_vec(n: nat) -> Vec<char>
  decreases n
  ensures Str2Int(result@) == n
  ensures ValidBitString(result@)
{
    if n == 0 {
        let v: Vec<char> = Vec::new();
        return v;
    } else {
        let mut prefix = nat_to_vec(n / 2);
        if n % 2 == 1 {
            prefix.push('1');
        } else {
            prefix.push('0');
        }
        proof {
            // Let lm be the index of the last bit
            let lm: int = prefix@.len() as int - 1;
            // By recursion, the prefix without last bit represents n/2
            assert(Str2Int(prefix@.subrange(0, lm)) == n / 2);
            // The last pushed bit corresponds to n % 2
            assert(prefix@.index(lm) == (if n % 2 == 1 { '1' } else { '0' }));
            // Unfold Str2Int definition for non-empty sequence
            assert(Str2Int(prefix@) == 2 * Str2Int(prefix@.subrange(0, lm)) + (if prefix@.index(lm) == '1' { 1 } else { 0 }));
            // Use division identity to conclude equality with n
            lemma_div_mod_2(n);
            assert(Str2Int(prefix@) == n);
        }
        return prefix;
    }
}

exec fn pow_mod(a: nat, e: nat, m: nat) -> nat
  requires m > 0
  ensures result == Exp_int(a, e) % m
  decreases e
{
    if e == 0 {
        1 % m
    } else {
        let prev = pow_mod(a, e - 1, m);
        let res = (prev * a) % m;
        proof {
            assert(prev == Exp_int(a, e - 1) % m);
            lemma_mod_mul(m, Exp_int(a, e - 1), a);
            assert(((Exp_int(a, e - 1) % m) * a) % m == (Exp_int(a, e - 1) * a) % m);
            assert(Exp_int(a, e) == a * Exp_int(a, e - 1));
            assert(res == Exp_int(a, e) % m);
        }
        res
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_int(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let a: nat = slice_to_nat(sx);
    let e: nat = slice_to_nat(sy);
    let m: nat = slice_to_nat(sz);

    let acc: nat = pow_mod(a, e, m);

    let res = nat_to_vec(acc);
    res
}
// </vc-code>

fn main() {}
}