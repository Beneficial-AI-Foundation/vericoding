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
/* helper modified by LLM (iteration 5): Corrected type of 'exp' */
spec fn power_of_2(exp: nat) -> nat {
    if exp == 0 {
        1
    } else {
        2 * power_of_2((exp - 1) as nat)
    }
}
// </vc-helpers>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed type errors related to `nat` and `int`, and improved array indexing proofs. */
{
    use std::ops::Index;

    let n1 = Str2Int(s1@);
    let n2 = Str2Int(s2@);
    let product: nat = n1 * n2;
    let mut result: Vec<char> = Vec::new();

    if product == 0 {
        result.push('0');
        return result;
    }

    let mut temp = product;
    while temp > 0
    invariant
        product == temp * power_of_2(result.len() as nat) + Str2Int(result@),
        forall |i: int| 0 <= i && i < result.len() ==> (result.index(i) == '0' || result.index(i) == '1')
    {
        if temp % 2 == 1 {
            result.push('1');
        } else {
            result.push('0');
        }
        temp = temp / 2;
    }
    
    // The bits are generated in reverse order, so we need to reverse the Vek
    let mut reversed_result: Vec<char> = Vec::new();
    let mut i: usize = result.len();
    while i > 0
    invariant
        i <= result.len(),
        reversed_result.len() == result.len() - i,
        forall |j: usize| 0 <= j && (j < (reversed_result.len() as usize)) ==> 
            (reversed_result.index(j) == result.index(result.len() - 1 - j))
    {
        i = i - 1;
        reversed_result.push(result.index(i));
    }

    reversed_result
}
// </vc-code>

fn main() {}
}


