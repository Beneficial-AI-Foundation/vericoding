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
  // All characters must be '0' or '1'.
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-spec>
exec fn NormalizeBitString(s: &[char]) -> (t: Vec<char>)
  ensures ValidBitString(t@),
   t@.len() > 0,
   t@.len() > 1 ==> t@[0] != '0',
   ValidBitString(s@) ==> Str2Int(s@) == Str2Int(t@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed NormalizeBitString with improved verification */
{
    let mut t = s.to_vec();
    while t.len() > 1 && t[0] == '0'
        invariant
            ValidBitString(t@),
            t@.len() > 0,
            Str2Int(s@) == Str2Int(t@),
    {
        t.remove(0);
    }
    if t.is_empty() {
        t.push('0');
    }
    t
}
// </vc-code>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed minimum_nat function with proper result variable */
spec fn minimum_nat(a: nat, b: nat) -> nat 
  ensures
      result <= a,
      result <= b,
      result == a || result == b
{
  if a <= b { a } else { b }
}

/* helper modified by LLM (iteration 5): Added pow2 helper function */
spec fn pow2(exp: nat) -> nat {
    if exp == 0 {
        1nat
    } else {
        2 * pow2(exp - 1)
    }
}
// </vc-helpers>

// <vc-spec>
exec fn Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@),
   ValidBitString(s2@),
  ensures ValidBitString(res@), 
    Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed Add implementation with proper pow2 import */
{
    let n1 = Str2Int(s1@);
    let n2 = Str2Int(s2@);
    let sum = n1 + n2;
    let mut result = Vec::new();
    if sum == 0 {
        result.push('0');
    } else {
        let mut n = sum;
        while n > 0
            invariant
                ValidBitString(result@),
                Str2Int(result@) + n * pow2(result.len() as nat) == sum,
        {
            if n % 2 == 1 {
                result.push('1');
            } else {
                result.push('0');
            }
            n = n / 2;
        }
        result.reverse();
    }
    result
}
// </vc-code>

fn main() {}
}


