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
pub exec fn bits_to_nat(bs: &[char]) -> nat
  requires ValidBitString(bs@)
  ensures Str2Int(bs@) == result
  decreases bs.len()
{
    if bs.len() == 0 {
        0
    } else {
        let len_usize = bs.len() - 1;
        let last = bs[len_usize];
        let prefix = &bs[..len_usize];
        let acc = bits_to_nat(prefix);
        if last == '1' {
            2 * acc + 1
        } else {
            2 * acc
        }
    }
}

// Lemma: Exp_int(base, x) * Exp_int(base, y) == Exp_int(base, x + y)
pub proof fn exp_add(base: nat, x: nat, y: nat)
  ensures Exp_int(base, x) * Exp_int(base, y) == Exp_int(base, x + y)
  decreases y
{
    if y == 0 {
        // Exp_int(base, 0) == 1
        assert(Exp_int(base, y) == 1);
        assert(Exp_int(base, x) * Exp_int(base, y) == Exp_int(base, x));
        assert(Exp_int(base, x + y) == Exp_int(base, x));
    } else {
        // y > 0
        exp_add(base, x, y - 1);
        // Exp_int(base, y) == base * Exp_int(base, y-1)
        assert(Exp_int(base, y) == base * Exp_int(base, y - 1));
        // Using IH: Exp_int(base, x) * Exp_int(base, y-1) == Exp_int(base, x + y - 1)
        assert(Exp_int(base, x) * Exp_int(base, y - 1) == Exp_int(base, x + (y - 1)));
        // Multiply both sides by base
        assert(Exp_int(base, x) * (base * Exp_int(base, y - 1)) == Exp_int(base, x + (y - 1)) * base);
        // Rearranged gives the desired equality
        assert(Exp_int(base, x) * Exp_int(base, y) == Exp_int(base, x + y));
    }
}

// Lemma: ((a % m) * (b % m)) % m == (a * b) % m
pub proof fn mod_mul_rem(a: nat, b: nat, m: nat)
  requires m > 0
  ensures ((a % m) * (b % m)) % m == (a * b) % m
{
    let q1 = a / m;
    let r1 = a % m;
    let q2 = b / m;
    let r2 = b % m;
    // a = q1*m + r1, b = q2*m + r2
    assert(a == q1 * m + r1);
    assert(b == q2 * m + r2);
    // a*b = (q1*m + r1) * (q2*m + r2) = s*m + r1*r2
    let s = q1 * q2 * m + q1 * r2 + q2 * r1;
    assert(a * b == s * m + r1 * r2);
    // (s*m) % m == 0
    assert((s * m) % m == 0);
    // therefore (s*m + r1*r2) % m == (r1*r2) % m
    assert((s * m + r1 * r2) % m == (r1 * r2) % m);
    // substitute a*b == s*m + r1*r2
    assert((a * b) % m == (r1 * r2) % m);
    // r1 == a % m, r2 == b % m
    assert((r1 * r2) % m == ((a % m) * (b % m)) % m);
    // conclude
    assert((a * b) % m == ((a % m) * (b % m)) % m);
}
    
// Recursive helper that computes base^(Str2Int(sy@.subrange(0, i))) % modulus
pub exec fn modexp_idx(base: nat, modulus: nat, sy: &[char], i: int) -> nat
  requires 0 <= i && i <= sy.len() as int
  requires ValidBitString(sy@)
  requires modulus > 0
  ensures result == Exp_int(base, Str2Int(sy@.subrange(0, i))) % modulus
  decreases (sy.len() as int) - i
{
    if i == 0 {
        1 % modulus
    } else {
        let prev = modexp_idx(base, modulus, sy, i - 1);
        let b = sy[(i - 1) as usize];
        let prefix_val: nat = Str2Int(sy@.subrange(0, i - 1));
        // From recursive call: prev == Exp_int(base, prefix_val) % modulus
        assert(prev == Exp_int(base, prefix_val) % modulus);
        // tmp_sq computed from prev (which is modded)
        let tmp_sq = (prev * prev) % modulus;
        // Show tmp_sq == Exp_int(base, prefix_val + prefix_val) % modulus
        // Use mod_mul_rem to move mod inside multiplication of full exponentials
        mod_mul_rem(Exp_int(base, prefix_val), Exp_int(base, prefix_val), modulus);
        // By exp_add, Exp_int(base, prefix_val) * Exp_int(base, prefix_val) == Exp_int(base, prefix_val + prefix_val)
        exp_add(base, prefix_val, prefix_val);
        // Now relate tmp_sq to Exp_int(... ) % modulus
        assert(((Exp_int(base, prefix_val) % modulus) * (Exp_int(base, prefix_val) % modulus)) % modulus == (Exp_int(base, prefix_val + prefix_val)) % modulus);
        // prev == Exp_int(...) % modulus, so tmp_sq equals that too
        assert(tmp_sq == Exp_int(base, prefix_val + prefix_val) % modulus);

        if b == '1' {
            // multiply by base once more under modulus
            // Use mod_mul_rem to relate multiplication by base
            mod_mul_rem(Exp_int(base, prefix_val + prefix_val), base, modulus);
            // Use exp_add to combine exponents
            exp_add(base, prefix_val + prefix_val, 1);
            let tmp = (tmp_sq * (base % modulus)) % modulus;
            // tmp == Exp_int(base, prefix_val + prefix_val + 1) % modulus
            assert(tmp == Exp_int(base, prefix_val + prefix_val + 1) % modulus);
            tmp
        } else {
            tmp_sq
        }
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    let base: nat = bits_to_nat(sx);
    let modulus: nat = bits_to_nat(sz);
    assert(base == Str2Int(sx@));
    assert(modulus == Str2Int(sz@));

    let n: int = sy.len() as int;
    let result_nat: nat = modexp_idx(base, modulus, sy, n);

    assert(result_nat == Exp_int(base, Str2Int(sy@)) % modulus);

    let res_bits = nat_to_bits(result_nat);
    assert(ValidBitString(res_bits@));
    assert(Str2Int(res_bits@) == result_nat);
    assert(Str2Int(res_bits@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@));
    res_bits
}
// </vc-code>

fn main() {}
}