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
/* helper modified by LLM (iteration 2): fixed nat literal comparisons and operations */
exec fn binary_multiply(a: nat, b: nat) -> (result: Vec<char>)
    ensures
        ValidBitString(result@),
        Str2Int(result@) == a * b
{
    let mut result = Vec::new();
    let mut temp = a * b;
    if temp == 0nat {
        result.push('0');
    } else {
        let mut digits = Vec::new();
        while temp > 0nat
            invariant
                temp >= 0nat,
                ValidBitString(digits@)
        {
            if temp % 2nat == 1nat {
                digits.push('1');
            } else {
                digits.push('0');
            }
            temp = temp / 2nat;
        }
        let mut i = digits.len();
        while i > 0
            invariant
                i <= digits.len(),
                ValidBitString(result@)
        {
            i = i - 1;
            result.push(digits[i]);
        }
    }
    result
}
// </vc-helpers>

// <vc-spec>
exec fn Mul_Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed function call with proper type handling */
    let a = Str2Int(s1@);
    let b = Str2Int(s2@);
    binary_multiply(a, b)
}
// </vc-code>

fn main() {}
}
