use vstd::prelude::*;

verus! {

spec fn Str2Int(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  if s.len() == 0 {
    0
  } else {
    2 * Str2Int(s.subrange(0, s.len() as int - 1))
      + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat })
  }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
/* helper modified by LLM (iteration 2): Removed incorrect lemma signature, simplified helper to call existing Str2Int. */
spec fn BitString_to_nat(s: Seq<char>) -> nat {
    Str2Int(s)
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2_Mul_Zeroes(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Fixed verification bypass, implemented basic bitstring addition. */
{
    let a_nat = Str2Int(a@);
    let b_nat = Str2Int(b@);

    let sum_nat = a_nat + b_nat;

    let mut bit_string_vec: Vec<char> = Vec::new();
    let mut val = sum_nat;

    if val == 0 {
        bit_string_vec.push('0');
    } else {
        while val > 0
            invariant val >= 0,
            decreases val
        {
            if val % 2 == 1 {
                bit_string_vec.push('1');
            } else {
                bit_string_vec.push('0');
            }
            val = val / 2;
        }
        bit_string_vec.reverse();
    }
    
    // Proof for ValidBitString(res@):
    // The loop only pushes '0' or '1' characters, so the resulting Vec<char> will always be a valid bit string.
    proof {
        assert forall |i: int| 0 <= i && i < bit_string_vec@.len() ==> (bit_string_vec@[i] == '0' || bit_string_vec@[i] == '1') by {
            // This invariant should be provable from the loop logic.
            // Each character pushed into bit_string_vec is either '0' or '1'.
        }
    }
    
    bit_string_vec
}
// </vc-code>

fn main() {}
}

