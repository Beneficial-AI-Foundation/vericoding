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
/* helper modified by LLM (iteration 2): Removed Exp_int(Exp_int(base, remaining_exp), 2) to fix a compilation error related to not having explicity `as nat` for the argument of `Exp_int`*/
proof fn lemma_msb_exp_int(base: nat, exp: nat, modulus: nat)
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
          assert(Exp_int(base, exp) == Exp_int(base, (2 * remaining_exp + 1) as nat)) by(nonlinear_arith);
          assert(Exp_int(base, exp) == base * Exp_int(base, (2 * remaining_exp) as nat)) by(nonlinear_arith);
          assert(Exp_int(base, exp) == base * Exp_int(base*base, remaining_exp)) by(bit_vector, nonlinear_arith);

          lemma_msb_exp_int(base, remaining_exp, modulus);
          assert(Exp_int_recursive_helper(base, remaining_exp_bits, modulus) == Exp_int(base, remaining_exp) % modulus);

          let val_remaining_mod = Exp_int(base, remaining_exp) % modulus;
          let squared_val_mod = (val_remaining_mod * val_remaining_mod) % modulus;
          let result = (squared_val_mod * (base % modulus)) % modulus;

          assert(Exp_int(base, exp) % modulus == result) by(nonlinear_arith);

          assert(Exp_int_recursive_helper(base, exp_bits, modulus) == result) by(nonlinear_arith);
        } else {
          assert(exp == 2 * remaining_exp);
          assert(Exp_int(base, exp) == Exp_int(base, (2 * remaining_exp) as nat)) by(nonlinear_arith);
          assert(Exp_int(base, exp) == Exp_int(base*base, remaining_exp)) by(bit_vector, nonlinear_arith);

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
/* code modified by LLM (iteration 2): Corrected the invariant for result_val and added an intermediate variable for clarity */
{
        let x_val = Str2Int(sx@);
        let y_val = Str2Int(sy@);
        let z_val = Str2Int(sz@);

        let base = x_val % z_val;
        let mut result_val: nat = 1;

        let mut exp_bits = sy@;

        while exp_bits.len() > 0
            invariant
                ValidBitString(sy@),
                ValidBitString(exp_bits),
                z_val > 1,
                sy@.len() > 0,
                base == Str2Int(sx@) % z_val,
                result_val == Exp_int_recursive_helper(base, sy@.subrange(exp_bits.len(), sy@.len()), z_val)
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
        let mut current_val: nat = result_val;

        if current_val == 0 {
            result_seq = seq!['0'];
        } else {
            while current_val > 0
                invariant
                    ValidBitString(result_seq),
                    current_val + (Str2Int(result_seq) * Exp_int(2, result_seq.len() as nat)) == result_val,
                    result_val == Str2Int(sy@).add_variant
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


