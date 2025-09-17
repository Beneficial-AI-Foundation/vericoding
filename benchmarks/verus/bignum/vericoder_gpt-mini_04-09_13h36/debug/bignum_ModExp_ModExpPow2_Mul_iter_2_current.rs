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
// Helper: convert a vector/sequence of '0'/'1' (MSB-first, last char is LSB) to nat
exec fn seq_to_nat(s: &[char]) -> nat
  requires ValidBitString(s@)
  ensures result == Str2Int(s@)
{
    let mut r: nat = 0;
    let mut i: usize = 0;
    while i < s.len() {
        invariant i <= s.len();
        invariant r == Str2Int(s@.subrange(0, i as int));
        {
            let b: nat = if s[i] == '1' { 1 } else { 0 };
            r = 2 * r + b;
            i += 1;
        }
    }
    r
}

// Helper: convert nat to sequence of '0'/'1' (MSB-first, last char is LSB)
// Decreasing on n ensures termination
exec fn nat_to_seq(n: nat) -> Vec<char>
  ensures Str2Int(result@) == n && ValidBitString(result@)
  decreases n
{
    if n == 0 {
        Vec::<char>::new()
    } else {
        let mut prefix = nat_to_seq(n / 2);
        let bit = if n % 2 == 1 { '1' } else { '0' };
        prefix.push(bit);
        prefix
    }
}

// Lemma: (a*a) ^ k == a ^ (2*k)
proof fn lemma_exp_pow2(a: nat, k: nat)
  ensures Exp_int(a * a, k) == Exp_int(a, 2 * k)
  decreases k
{
    if k == 0 {
        // both sides are 1
        assert(Exp_int(a * a, 0) == 1);
        assert(Exp_int(a, 0) == 1);
    } else {
        lemma_exp_pow2(a, k - 1);
        // Exp_int(a*a, k) = (a*a) * Exp_int(a*a, k-1)
        assert(Exp_int(a * a, k) == (a * a) * Exp_int(a * a, k - 1));
        // By IH, Exp_int(a*a, k-1) == Exp_int(a, 2*(k-1))
        assert(Exp_int(a * a, k - 1) == Exp_int(a, 2 * (k - 1)));
        // So Exp_int(a*a, k) = a*a * Exp_int(a, 2*k - 2)
        assert(Exp_int(a * a, k) == a * a * Exp_int(a, 2 * k - 2));
        // Exp_int(a, 2*k) = a * Exp_int(a, 2*k - 1) = a * (a * Exp_int(a, 2*k - 2))
        assert(Exp_int(a, 2 * k) == a * (a * Exp_int(a, 2 * k - 2)));
        // therefore equal
        assert(Exp_int(a * a, k) == Exp_int(a, 2 * k));
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
    // Convert inputs to nats
    let x = seq_to_nat(sx);
    let y = seq_to_nat(sy);
    let m = seq_to_nat(sz);

    // Prepare variables for exponentiation
    let mut base_full: nat = x; // will hold x^(2^k) (full nat, not modded)
    let mut exp: nat = y;
    let mut res_mod: nat = 1 % m; // always maintained modulo m

    // Loop invariant:
    //   0 <= exp <= y
    //   (res_mod * Exp_int(base_full, exp)) % m == Exp_int(x, y) % m
    // Decreases on exp (dividing by 2 guarantees strict decrease when exp > 0)
    while exp > 0
        invariant exp <= y
        invariant (res_mod * Exp_int(base_full, exp)) % m == Exp_int(x, y) % m
        decreases exp
    {
        if exp % 2 == 1 {
            // incorporate lowest bit
            res_mod = (res_mod * base_full) % m;
        }
        // square the base and shift exponent right
        let exp_new = exp / 2;
        let base_new = base_full * base_full;

        // Proof that invariant is preserved:
        proof {
            // Let bit = exp % 2, exp = 2*exp_new + bit
            let bit: nat = exp % 2;
            // Use lemma: Exp_int(base_new, exp_new) == Exp_int(base_full, 2*exp_new)
            lemma_exp_pow2(base_full, exp_new);
            // Now reason about the two cases
            if bit == 1 {
                // Old invariant:
                //   (res_mod * Exp_int(base_full, exp)) % m == Exp_int(x, y) % m
                // Exp_int(base_full, exp) = base_full * Exp_int(base_full, 2*exp_new)
                assert(Exp_int(base_full, exp) == base_full * Exp_int(base_full, 2 * exp_new));
                // Using lemma, Exp_int(base_new, exp_new) == Exp_int(base_full, 2*exp_new)
                assert(Exp_int(base_new, exp_new) == Exp_int(base_full, 2 * exp_new));
                // After update res_mod' = (res_mod * base_full) % m
                // We need to show (res_mod' * Exp_int(base_new, exp_new)) % m == Exp_int(x, y) % m
                // Compute LHS:
                //   ( (res_mod * base_full) * Exp_int(base_new, exp_new) ) % m
                // = ( res_mod * (base_full * Exp_int(base_full, 2*exp_new)) ) % m
                // = ( res_mod * Exp_int(base_full, exp) ) % m
                // which equals RHS by old invariant.
                assert((res_mod * base_full * Exp_int(base_new, exp_new)) % m == (res_mod * Exp_int(base_full, exp)) % m);
                assert((res_mod * base_full * Exp_int(base_new, exp_new)) % m == Exp_int(x, y) % m);
            } else {
                // bit == 0
                // Exp_int(base_full, exp) = Exp_int(base_full, 2*exp_new)
                assert(Exp_int(base_full, exp) == Exp_int(base_full, 2 * exp_new));
                // Using lemma, Exp_int(base_new, exp_new) == Exp_int(base_full, 2*exp_new)
                assert(Exp_int(base_new, exp_new) == Exp_int(base_full, 2 * exp_new));
                // res_mod unchanged, so
                assert((res_mod * Exp_int(base_new, exp_new)) % m == (res_mod * Exp_int(base_full, exp)) % m);
                assert((res_mod * Exp_int(base_new, exp_new)) % m == Exp_int(x, y) % m);
            }
        }
// </vc-code>

fn main() {}
}