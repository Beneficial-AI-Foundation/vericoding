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
  // All characters must be '0' or '1'.
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

spec fn AllZero(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==> s.index(i) == '0'
}

// <vc-helpers>
spec fn subrange_to_seq(s_slice: &[char], start: int, end: int) -> Seq<char>
    requires 0 <= start <= end <= s_slice.len()
{
    s_slice@.subrange(start, end)
}

spec fn get_pow_2(n: nat) -> nat
{
    if n == 0 { 1 }
    else { 2 * get_pow_2((n - 1) as nat) }
}

proof fn pow2_monotonic(n: nat) 
    ensures get_pow_2(n) > 0
{
    if n == 0 {}
    else { pow2_monotonic((n - 1) as nat); }
}

proof fn Exp_int_base_2_is_pow2(n: nat)
    ensures Exp_int(2, n) == get_pow_2(n)
{
    if n == 0 { } else { Exp_int_base_2_is_pow2((n - 1) as nat); }
}

// Lemma to prove Str2Int of a sequence padded with '0's is equivalent to the original.
proof fn lemma_str2int_padded(s: Seq<char>, padding_len: nat)
    requires ValidBitString(s)
    ensures
        (#[trigger] Str2Int(s.add(Seq::new(padding_len as int, |i:int| '0')))) == Str2Int(s) * Exp_int(2, padding_len) 
{
    if padding_len == 0 { } else {
        lemma_str2int_padded(s, (padding_len - 1) as nat);
    }
}

proof fn lemma_mult_mod_distrib(a: nat, b: nat, c:nat, m: nat)
    requires m > 0
    ensures (a * b) % m == ((a % m) * (b % m)) % m
{}

proof fn lemma_power_of_two_mod(n: nat, m: nat)
    requires m > 0
    ensures Exp_int(2, n) % m == Exp_int(2 % m, n) % m
{
    // We are trying to prove Exp_int(2, n) % m == Exp_int(2 % m, n) % m
    // This is generally true for (a^n) % m == ((a % m)^n) % m
    // Proof by induction
    if n == 0 {
        assert(Exp_int(2, 0) % m == 1 % m) by (nonlinear_arith);
        assert(Exp_int(2 % m, 0) % m == 1 % m) by (nonlinear_arith);
    } else {
        // Inductive step
        // Exp_int(A, n) = A * Exp_int(A, n-1)
        // We need (2 * Exp_int(2, n-1)) % m == ((2 % m) * Exp_int(2 % m, n-1)) % m
        // Let A = 2, B = Exp_int(2, n-1), C = 2 % m, D = Exp_int(2 % m, n-1)
        // We know from induction hypothesis that B % m == D % m
        // We want to show (A*B) % m == (C*D) % m
        // (A*B) % m == ((A % m) * (B % m)) % m (lemma_mult_mod_distrib)
        // (C*D) % m == ((C % m) * (D % m)) % m (lemma_mult_mod_distrib)
        // Since A % m == C % m (both 2 % m)
        // And B % m == D % m (IH)
        // Then (A*B % m) == (C*D % m)
        lemma_power_of_two_mod((n - 1) as nat, m);
        lemma_mult_mod_distrib(2, Exp_int(2, (n - 1) as nat), (2 % m), Exp_int(2 % m, (n - 1) as nat) as nat);
    }
}


pub closed spec fn Exp_int_recursive_helper(base: nat, exp_bits: Seq<char>, modulus: nat) -> nat
    recommends ValidBitString(exp_bits)
    decreases exp_bits.len()
{
    if exp_bits.len() == 0 {
        1
    } else {
        let last_bit = exp_bits.index(exp_bits.len() - 1);
        let remaining_exp_bits = exp_bits.subrange(0, exp_bits.len() - 1);
        let val_remaining = Exp_int_recursive_helper(base, remaining_exp_bits, modulus);
        let squared_val_mod = (val_remaining * val_remaining) % modulus;

        if last_bit == '1' {
            (squared_val_mod * base) % modulus
        } else {
            squared_val_mod
        }
    }
}

pub proof fn lemma_msb_exp_int(base: nat, exp: nat, modulus: nat)
    requires modulus > 0
    ensures
        Exp_int(base, exp) % modulus == Exp_int_recursive_helper(base, int_to_bit_seq(exp), modulus)

{
    if exp == 0 {
        assert(Exp_int(base, 0) % modulus == 1 % modulus);
        assert(Exp_int_recursive_helper(base, int_to_bit_seq(0), modulus) == 1);
    } else {
        // Proof by induction on exp
        let exp_bits = int_to_bit_seq(exp);
        let msb = exp_bits.last();
        let remaining_exp_bits = exp_bits.drop_last();
        let remaining_exp = Str2Int(remaining_exp_bits);

        if (msb == '1') {
          assert(exp == 2 * remaining_exp + 1);
          assert(Exp_int(base, exp) == Exp_int(base, 2 * remaining_exp + 1)) by(nonlinear_arith);
          assert(Exp_int(base, exp) == base * Exp_int(base, 2 * remaining_exp)) by(nonlinear_arith);
          assert(Exp_int(base, exp) == base * Exp_int(Exp_int(base, remaining_exp), 2)) by(bit_vector, nonlinear_arith);

          lemma_msb_exp_int(base, remaining_exp, modulus);
          assert(Exp_int_recursive_helper(base, remaining_exp_bits, modulus) == Exp_int(base, remaining_exp) % modulus);

          let val_remaining_mod = Exp_int(base, remaining_exp) % modulus;
          let squared_val_mod = (val_remaining_mod * val_remaining_mod) % modulus;
          let result = (squared_val_mod * (base % modulus)) % modulus;

          assert(Exp_int(base, exp) % modulus == result) by(nonlinear_arith);

          assert(Exp_int_recursive_helper(base, exp_bits, modulus) == result) by(nonlinear_arith);
        } else {
          assert(exp == 2 * remaining_exp);
          assert(Exp_int(base, exp) == Exp_int(base, 2 * remaining_exp)) by(nonlinear_arith);
          assert(Exp_int(base, exp) == Exp_int(Exp_int(base, remaining_exp), 2)) by(bit_vector, nonlinear_arith);

          lemma_msb_exp_int(base, remaining_exp, modulus);
          assert(Exp_int_recursive_helper(base, remaining_exp_bits, modulus) == Exp_int(base, remaining_exp) % modulus);

          let val_remaining_mod = Exp_int(base, remaining_exp) % modulus;
          let squared_val_mod = (val_remaining_mod * val_remaining_mod) % modulus;
          let result = squared_val_mod;

          assert(Exp_int(base, exp) % modulus == result) by(nonlinear_arith);

          assert(Exp_int_recursive_helper(base, exp_bits, modulus) == result) by(nonlinear_arith);
        }
    }
}

spec fn int_to_bit_seq(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 { Seq::empty() }
    else {
        let bit = if n % 2 == 1 { '1' } else { '0' };
        int_to_bit_seq(n / 2).push(bit)
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
        let x_val = Str2Int(sx@);
        let y_val = Str2Int(sy@);
        let z_val = Str2Int(sz@);

        let base = x_val % z_val;
        let mut result_val = 1nat;

        let mut exp_bits = sy@;

        while exp_bits.len() > 0
            invariant
                ValidBitString(sy@),
                ValidBitString(exp_bits),
                z_val > 1,
                sy@.len() > 0,
                base == Str2Int(sx@) % z_val,
                result_val == Exp_int_recursive_helper(Str2Int(sx@) % z_val, sy@.subrange(exp_bits.len(), sy@.len()), z_val)

            decreases exp_bits.len()
        {
            let msb = exp_bits.last();
            let remaining_exp_bits = exp_bits.drop_last();

            // Square the current result
            result_val = (result_val * result_val) % z_val;

            // If the last bit of the exponent is '1', multiply by the base
            if msb == '1' {
                result_val = (result_val * base) % z_val;
            }

            exp_bits = remaining_exp_bits;
        }

        lemma_msb_exp_int(Str2Int(sx@), Str2Int(sy@), z_val);

        // Convert the final nat result back to a bit string representation
        let mut result_seq = Seq::<char>::empty();
        let mut current_val = result_val;

        if current_val == 0 {
            result_seq = seq!['0'];
        } else {
            while current_val > 0
                invariant
                    ValidBitString(result_seq),
                    current_val + (Str2Int(result_seq) * Exp_int(2, result_seq.len())) == result_val

                decreases current_val
            {
                let bit = if current_val % 2 == 1 { '1' } else { '0' };
                result_seq = seq![bit].add(result_seq);
                current_val = current_val / 2;
            }
        }

        result_seq.to_vec()
    }
// </vc-code>

fn main() {}
}


