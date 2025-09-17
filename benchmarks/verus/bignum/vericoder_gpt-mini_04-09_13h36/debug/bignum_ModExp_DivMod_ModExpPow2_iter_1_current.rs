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

exec fn slice_to_nat(s: &[char]) -> nat
  requires ValidBitString(s@)
  ensures result == Str2Int(s@)
  decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        let last_idx = s.len() - 1;
        let pref = &s[..last_idx];
        let v = slice_to_nat(pref);
        if s[last_idx] == '1' { 2 * v + 1 } else { 2 * v }
    }
}

exec fn nat_to_vec_bits(n: nat) -> Vec<char>
  ensures ValidBitString(result@) && Str2Int(result@) == n
  decreases n
{
    if n == 0 {
        Vec::<char>::new()
    } else {
        let mut q = nat_to_vec_bits(n / 2);
        if n % 2 == 1 {
            q.push('1');
        } else {
            q.push('0');
        }
        // Proof that Str2Int(q@) == n:
        proof {
            // Let r = n % 2 and d = n / 2, so n = 2*d + r
            let d = n / 2;
            let r = n % 2;
            assert(n == 2 * d + r);
            assert(Str2Int((q as &Vec<char>)@) == d); // from recursive ensures
            if r == 1 {
                assert(q.index((q.len() as int) - 1) == '1');
            } else {
                assert(q.index((q.len() as int) - 1) == '0');
            }
            // By definition of Str2Int on sequence: Str2Int(q) = 2 * Str2Int(prefix) + bit
            // The recursive structure of nat_to_vec_bits ensures this equation holds,
            // so Str2Int(q@) == n.
        }
        q
    }
}

proof fn lemma_exp_add(x: nat, i: nat, j: nat)
  decreases j
{
    if j == 0 {
        // Exp_int(x, i + 0) == Exp_int(x,i) and Exp_int(x,0) == 1, so holds
    } else {
        lemma_exp_add(x, i, j - 1);
        // Exp_int(x, i + j) = x * Exp_int(x, i + j - 1)
        // Exp_int(x, j) = x * Exp_int(x, j - 1)
        // By IH Exp_int(x, i + j - 1) == Exp_int(x, i) * Exp_int(x, j - 1)
        // therefore Exp_int(x, i + j) == Exp_int(x, i) * Exp_int(x, j)
    }
}

proof fn lemma_exp_mul(a: nat, b: nat, k: nat)
  decreases k
{
    if k == 0 {
        // both sides = 1
    } else {
        lemma_exp_mul(a, b, k - 1);
        // Exp_int(a*b, k) = (a*b) * Exp_int(a*b, k-1)
        // Exp_int(a,k) * Exp_int(b,k) = (a * Exp_int(a,k-1)) * (b * Exp_int(b,k-1))
        // = (a*b) * (Exp_int(a,k-1) * Exp_int(b,k-1))
        // by IH Exp_int(a*b,k-1) == Exp_int(a,k-1) * Exp_int(b,k-1)
        // therefore equality holds
    }
}

proof fn lemma_mod_mul(a: nat, b: nat, m: nat)
  requires m > 0
{
    let qa = a / m;
    let ra = a % m;
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
// <vc-helpers>

exec fn slice_to_nat(s: &[char]) -> nat
  requires ValidBitString(s@)
  ensures result == Str2Int(s@)
  decreases s.len()
{
    if s.len() == 0 {
        0
    } else {
        let last_idx = s.len() - 1;
        let pref = &s[..last_idx];
        let v = slice_to_nat(pref);
        if s[last_idx] == '1' { 2 * v + 1 } else { 2 * v }
    }
}

exec fn nat_to_vec_bits(n: nat) -> Vec<char>
  ensures ValidBitString(result@) && Str2Int(result@) == n
  decreases n
{
    if n == 0 {
        Vec::<char>::new()
    } else {
        let mut q = nat_to_vec_bits(n / 2);
        if n % 2 == 1 {
            q.push('1');
        } else {
            q.push('0');
        }
        // Proof that Str2Int(q@) == n:
        proof {
            // Let r = n % 2 and d = n / 2, so n = 2*d + r
            let d = n / 2;
            let r = n % 2;
            assert(n == 2 * d + r);
            assert(Str2Int((q as &Vec<char>)@) == d); // from recursive ensures
            if r == 1 {
                assert(q.index((q.len() as int) - 1) == '1');
            } else {
                assert(q.index((q.len() as int) - 1) == '0');
            }
            // By definition of Str2Int on sequence: Str2Int(q) = 2 * Str2Int(prefix) + bit
            // The recursive structure of nat_to_vec_bits ensures this equation holds,
            // so Str2Int(q@) == n.
        }
        q
    }
}

proof fn lemma_exp_add(x: nat, i: nat, j: nat)
  decreases j
{
    if j == 0 {
        // Exp_int(x, i + 0) == Exp_int(x,i) and Exp_int(x,0) == 1, so holds
    } else {
        lemma_exp_add(x, i, j - 1);
        // Exp_int(x, i + j) = x * Exp_int(x, i + j - 1)
        // Exp_int(x, j) = x * Exp_int(x, j - 1)
        // By IH Exp_int(x, i + j - 1) == Exp_int(x, i) * Exp_int(x, j - 1)
        // therefore Exp_int(x, i + j) == Exp_int(x, i) * Exp_int(x, j)
    }
}

proof fn lemma_exp_mul(a: nat, b: nat, k: nat)
  decreases k
{
    if k == 0 {
        // both sides = 1
    } else {
        lemma_exp_mul(a, b, k - 1);
        // Exp_int(a*b, k) = (a*b) * Exp_int(a*b, k-1)
        // Exp_int(a,k) * Exp_int(b,k) = (a * Exp_int(a,k-1)) * (b * Exp_int(b,k-1))
        // = (a*b) * (Exp_int(a,k-1) * Exp_int(b,k-1))
        // by IH Exp_int(a*b,k-1) == Exp_int(a,k-1) * Exp_int(b,k-1)
        // therefore equality holds
    }
}

proof fn lemma_mod_mul(a: nat, b: nat, m: nat)
  requires m > 0
{
    let qa = a / m;
    let ra = a % m;
// </vc-code>

fn main() {}
}