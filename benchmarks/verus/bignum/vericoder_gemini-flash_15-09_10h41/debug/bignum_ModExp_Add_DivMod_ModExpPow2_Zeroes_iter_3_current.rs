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

// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_DivMod_ModExpPow2_Zeroes(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Fixed type mismatches by casting `n` to `int` for comparison and arithmetic operations. Added `decreases n` to the loop. */
{
    let a_seq = a@;
    let b_seq = b@;

    let num_a = Str2Int(a_seq);
    let num_b = Str2Int(b_seq);

    let result_num = (num_a + num_b);

    let mut digits: Vec<char> = Vec::new();
    let mut n: nat = result_num;

    if (n as int) == 0 {
        digits.push('0');
    } else {
        while (n as int) > 0
            invariant
                n >= 0,
                forall |i: int| 0 <= i && i < digits.len() ==> (digits@[i] == '0' || digits@[i] == '1'),
            decreases n
        {
            if (n as int) % 2 == 1 {
                digits.push('1');
            } else {
                digits.push('0');
            }
            n = (n as nat) / 2;
        }
    }

    digits.reverse();
    digits
}
// </vc-code>

fn main() {}
}

