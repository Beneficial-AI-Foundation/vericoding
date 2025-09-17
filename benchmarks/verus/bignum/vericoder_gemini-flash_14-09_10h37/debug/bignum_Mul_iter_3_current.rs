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
/* helper modified by LLM (iteration 3): No change */
spec fn power_of_2(exp: nat) -> nat {
    if exp == 0 {
        1
    } else {
        2 * power_of_2(exp - 1)
    }
}
// </vc-helpers>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): Fixed compilation errors related to type conversion for `int` and `nat` */
{
    let n1 = Str2Int(s1@);
    let n2 = Str2Int(s2@);
    let product = n1 * n2;
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
    let mut i: int = result.len() as int - 1;
    while i >= 0
    invariant
        i >= -1,
        (reversed_result.len() as int) == (result.len() as int) - 1 - i,
        forall |j: int| 0 <= j && j < (reversed_result.len() as int) ==> 
            (reversed_result.index(j) == result.index((result.len() as int) - 1 - j))
    {
        reversed_result.push(result.index(i as nat));
        i = i - 1;
    }

    reversed_result
}
// </vc-code>

fn main() {}
}


