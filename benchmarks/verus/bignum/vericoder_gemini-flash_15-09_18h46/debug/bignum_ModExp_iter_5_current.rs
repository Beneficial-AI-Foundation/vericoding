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
/* helper modified by LLM (iteration 5): Removed redundant assert and simplified proof steps to address compilation error. */
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
      let two_remaining_exp = 2 * remaining_exp;
      assert(exp_val == two_remaining_exp + 1);
      assert(Exp_int(base_val, exp_val) == Exp_int(base_val, two_remaining_exp + 1))
        by(nonlinear_arith);
      assert(Exp_int(base_val, exp_val) == base_val * Exp_int(base_val, two_remaining_exp))
        by(nonlinear_arith);
      assert(Exp_int(base_val, exp_val) == base_val * Exp_int(base_val * base_val, remaining_exp))
        by(nonlinear_arith);

      lemma_msb_exp_int(base_val, remaining_exp, modulus);
    } else {
      let two_remaining_exp = 2 * remaining_exp;
      assert(exp_val == two_remaining_exp);
      assert(Exp_int(base_val, exp_val) == Exp_int(base_val, two_remaining_exp))
        by(nonlinear_arith);
      assert(Exp_int(base_val, exp_val) == Exp_int(base_val * base_val, remaining_exp))
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
/* code modified by LLM (iteration 5): Removed `Exp_int_recursive_helper` call to fix the compilation error. */
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
                base == Str2Int(sx@) % z_val
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

        lemma_msb_exp_int(x_val, y_val, z_val);

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
                    result_val >= 0
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


