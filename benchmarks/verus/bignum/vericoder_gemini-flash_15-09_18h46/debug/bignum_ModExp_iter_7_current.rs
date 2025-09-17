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
/* helper modified by LLM (iteration 7): Fixed compilation error with `push_back` on `Seq<char>` by converting to `Vec<char>` for manipulation, then back to `Seq` in the spec. Also, `Exp_int_recursive_helper_spec` needs a `recommends` clause and its `squared` computation needs `as nat` casts to avoid `mismatched types` errors. */
spec fn int_to_bit_seq(n: nat) -> Seq<char>
decreases n
{
  if n == 0 { seq!['0'] } else {
    let remainder = n % 2;
    let quotient = n / 2;
    if quotient == 0 {
      if remainder == 1 { seq!['1'] } else { seq!['0'] }
    } else {
      let mut s = int_to_bit_seq(quotient).to_vec();
      s.push(if remainder == 1 { '1' } else { '0' });
      s@
    }
  }
}

spec fn Exp_int_recursive_helper_spec(base: nat, exp_bits: Seq<char>, modulus: nat) -> nat
recommends modulus > 0
{
  if exp_bits.len() == 0 { 1 } else {
    let msb = exp_bits.last();
    let remaining_exp_bits = exp_bits.drop_last();
    let squared = (Exp_int_recursive_helper_spec(base, remaining_exp_bits, modulus) * Exp_int_recursive_helper_spec(base, remaining_exp_bits, modulus)) as nat
      % modulus;

    if msb == '1' {
      (squared * base) as nat % modulus
    } else {
      squared
    }
  }
}

proof fn lemma_msb_exp_int(base_val: nat, exp_val: nat, modulus: nat)
    requires modulus > 0
    ensures Exp_int(base_val, exp_val) % modulus == Exp_int_recursive_helper_spec(base_val % modulus, int_to_bit_seq(exp_val), modulus)
{
  if exp_val == 0 {
    assert(Exp_int(base_val, 0) == 1);
  } else {
    let exp_bits = int_to_bit_seq(exp_val);
    let msb = exp_bits.last();
    let remaining_exp_bits = exp_bits.drop_last();
    let remaining_exp = Str2Int(remaining_exp_bits);

    if msb == '1' {
      let two_remaining_exp = (2 * remaining_exp) as nat;
      assert(exp_val == two_remaining_exp + 1) by(nonlinear_arith);
      assert(Exp_int(base_val, exp_val) == Exp_int(base_val, (two_remaining_exp + 1) as nat))
        by(nonlinear_arith);
      assert(Exp_int(base_val, exp_val) == (base_val * Exp_int(base_val, two_remaining_exp)) as nat)
        by(nonlinear_arith);
      assert(Exp_int(base_val, exp_val) == Exp_int((base_val * base_val) as nat, remaining_exp))
        by(nonlinear_arith);

      lemma_msb_exp_int(base_val, remaining_exp, modulus);
    } else {
      let two_remaining_exp = (2 * remaining_exp) as nat;
      assert(exp_val == two_remaining_exp) by(nonlinear_arith);
      assert(Exp_int(base_val, exp_val) == Exp_int(base_val, two_remaining_exp))
        by(nonlinear_arith);
      assert(Exp_int(base_val, exp_val) == Exp_int((base_val * base_val) as nat, remaining_exp))
        by(nonlinear_arith);

      lemma_msb_exp_int(base_val, remaining_exp, modulus);
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
/* code modified by LLM (iteration 7): Fixed various type mismatch errors (expected `nat`, found `integer`) by explicitly casting to `nat` where necessary. Also, `result_seq.to_vec()` should be `result_seq.to_vec()` in the `return` statement. */
{
        let x_val = Str2Int(sx@);
        let y_val = Str2Int(sy@);
        let z_val = Str2Int(sz@);

        let base = (x_val % z_val) as nat;
        let mut result_val: nat = 1;

        let exp_bits_seq = int_to_bit_seq(y_val);
        let mut exp_bits = exp_bits_seq;

        while exp_bits.len() > (0 as nat)
            invariant
                ValidBitString(sy@),
                ValidBitString(exp_bits),
                z_val > (1 as nat),
                sy@.len() > (0 as nat),
                base == Str2Int(sx@) % z_val
            decreases exp_bits.len()
        {
            let msb = exp_bits.last();
            let remaining_exp_bits = exp_bits.drop_last();

            // Square the current result
            result_val = (result_val * result_val) as nat % z_val;

            // If the last bit of the exponent is '1', multiply by the base
            if msb == '1' {
                result_val = (result_val * base) as nat % z_val;
            }

            exp_bits = remaining_exp_bits;
        }

        lemma_msb_exp_int(x_val, y_val, z_val);

        // Convert the final nat result back to a bit string representation
        let mut result_seq = Seq::<char>::empty();
        let mut current_val: nat = result_val;

        if current_val == (0 as nat) {
            result_seq = seq!['0'];
        } else {
            while current_val > (0 as nat)
                invariant
                    ValidBitString(result_seq),
                    current_val + (Str2Int(result_seq) * Exp_int(2, result_seq.len() as nat)) == result_val,
                    result_val >= (0 as nat)
                decreases current_val
            {
                let bit = if current_val % (2 as nat) == (1 as nat) { '1' } else { '0' };
                result_seq = seq![bit].add(result_seq);
                current_val = (current_val / (2 as nat)) as nat;
            }
        }

        result_seq.to_vec()
    }
// </vc-code>

fn main() {}
}


