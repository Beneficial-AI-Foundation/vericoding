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
    let mut res_mod: nat = 1; // maintained modulo m; since m > 1, 1 < m

    // Loop invariant:
    //   exp <= y
    //   res_mod < m
    //   (res_mod * Exp_int(base_full, exp)) % m == Exp_int(x, y) % m
    while exp > 0
        invariant exp <= y
        invariant res_mod < m
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

        // Proof that invariant is preserved after assigning exp = exp_new and base_full = base_new
        proof {
            let bit: nat = exp % 2;
            // Use lemma: Exp_int(base_new, exp_new) == Exp_int(base_full, 2*exp_new)
            lemma_exp_pow2(base_full, exp_new);
            if bit == 1 {
                // Exp_int(base_full, exp) = base_full * Exp_int(base_full, 2*exp_new)
                assert(Exp_int(base_full, exp) == base_full * Exp_int(base_full, 2 * exp_new));
                // Using lemma, Exp_int(base_new, exp_new) == Exp_int(base_full, 2*exp_new)
                assert(Exp_int(base_new, exp_new) == Exp_int(base_full, 2 * exp_new));
                // After update res_mod' = (res_mod * base_full) % m
                // So (res_mod' * Exp_int(base_new, exp_new)) % m == (res_mod * base_full * Exp_int(base_new, exp_new)) % m
                // and by equalities above equals (res_mod * Exp_int(base_full, exp)) % m
                assert((res_mod * base_full * Exp_int(base_new, exp_new)) % m == (res_mod * Exp_int(base_full, exp)) % m);
                assert((res_mod * base_full * Exp_int(base_new, exp_new)) % m == Exp_int(x, y) % m);
            } else {
                // bit == 0
                // Exp_int(base_full, exp) = Exp_int(base_full, 2*exp_new)
                assert(Exp_int(base_full, exp) == Exp_int(base_full, 2 * exp_new));
                // Using lemma, Exp_int(base_new, exp_new) == Exp_int(base_full, 2*exp_new)
                assert(Exp_int(base_new, exp_new) == Exp_int(base_full, 2 * exp_new));
                // res_mod unchanged, so (res_mod * Exp_int(base_new, exp_new)) % m == (res_mod * Exp_int(base_full, exp)) % m
                assert((res_mod * Exp_int(base_new, exp_new)) % m == (res_mod * Exp_int(base_full, exp)) % m);
                assert((res_mod * Exp_int(base_new, exp_new)) % m == Exp_int(x, y) % m);
            }
            // Also res_mod < m is preserved because (a % m) < m and res_mod remains either unchanged (< m) or set to (something) % m (< m)
            // No extra proof needed as % yields < m when m > 0.
        }

        // perform the actual updates
        base_full = base_new;
        exp = exp_new;
    }

    // After loop, exp == 0
    // From invariant: (res_mod * Exp_int(base_full, 0)) % m == Exp_int(x, y) % m
    // So (res_mod * 1) % m == Exp_int(x, y) % m => res_mod % m == RHS
    // Since res_mod < m, res_mod % m == res_mod
    proof {
        assert(exp == 0);
        assert(Exp_int(base_full, 0) == 1);
        assert((res_mod * Exp_int(base_full, 0)) % m == Exp_int(x, y) % m);
        assert((res_mod * 1) % m == Exp_int(x, y) % m);
        assert(res_mod % m == Exp_int(x, y) % m);
        // res_mod < m implies res_mod % m == res_mod
        // hence res_mod == Exp_int(x, y) % m
    }

    // Return bitstring for res_mod
    nat_to_seq(res_mod)
}
// </vc-code>

fn main() {}
}