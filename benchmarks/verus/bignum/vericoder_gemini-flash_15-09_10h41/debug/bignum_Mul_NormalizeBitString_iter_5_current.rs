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
/* helper modified by LLM (iteration 5): Adding a helper function for `char_to_nat` and converting `nat_to_char` for robustness. */
/* helper modified by LLM (iteration 5): Added `char_to_nat` helper. */
spec fn char_to_nat(c: char) -> nat {
    if c == '0' { 0nat } else { 1nat }
}

spec fn nat_to_char(n: nat) -> char {
    if n == 0 { '0' } else { '1' }
}
// </vc-helpers>

// <vc-spec>
exec fn Mul_NormalizeBitString(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation error related to `nat` and integer operations. Cleaned up vector reversal loop conditions and indexing. */
{
    let i1 = Str2Int(s1@);
    let i2 = Str2Int(s2@);
    let prod: nat = i1 * i2;

    let mut result_vec = Vec::<char>::new();
    let mut current_prod: nat = prod;

    if current_prod == 0nat {
        result_vec.push('0');
    }

    while current_prod > 0nat
        invariant
            current_prod >= 0nat,
        decreases current_prod
    {
        if current_prod % 2 == 1nt {
            result_vec.push('1');
        } else {
            result_vec.push('0');
        }
        current_prod = current_prod / 2;
    }

    let mut reversed_result_vec = Vec::<char>::new();
    let mut i: int = result_vec.len() as int - 1;
    
    while i >= 0
        invariant
            i >= -1,
            (i as usize) < result_vec.len() || i == -1,
        decreases i
    {
        reversed_result_vec.push(result_vec@.index(i as usize));
        i = i - 1;
    }

    reversed_result_vec
}
// </vc-code>

fn main() {}
}
