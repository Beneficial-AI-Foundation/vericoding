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
/* code modified by LLM (iteration 10): Fixed NormalizeBitString to properly handle leading zeros and maintain bit string validity */
{
    let mut t = Vec::new();
    let mut i = 0;
    let mut found_non_zero = false;
    while i < s.len()
        invariant
            i >= 0,
            i <= s.len(),
            ValidBitString(t@),
            ValidBitString(s@) ==> Str2Int(s@) == Str2Int(t@),
            forall |j: int| 0 <= j && j < i ==> s@[j] == '0' ==> !found_non_zero
        decreases s.len() - i
    {
        let c = s[i];
        if c == '1' {
            t.push('1');
            found_non_zero = true;
            i += 1;
        } else if c == '0' {
            if found_non_zero {
                t.push('0');
            }
            i += 1;
        } else {
            proof { assert(false); }
        }
    }
    if t.is_empty() {
        t.push('0');
    }
    t
}
// </vc-code>

// <vc-spec>
exec fn CompareUnequal(s1: &[char], s2: &[char]) -> (res: i32)
  requires ValidBitString(s1@),
   ValidBitString(s2@),
   s1@.len() > 0,
   (s1@.len() > 1 ==> s1@[0] != '0'),
   s2@.len() > 0,
   (s2@.len() > 1 ==> s2@[0] != '0'),
   s1@.len() > s2@.len(),
  ensures Str2Int(s1@) < Str2Int(s2@) ==> res == -1,
    Str2Int(s1@) == Str2Int(s2@) ==> res == 0,
    Str2Int(s1@) > Str2Int(s2@) ==> res == 1
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Fixed CompareUnequal to use proper length-based logic */
{
    let n1 = s1.len() as nat;
    let n2 = s2.len() as nat;
    proof {
        str2int_length_lemma(s1@, s2@);
    }
    return 1;
}
// </vc-code>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Fixed pow2_nat to handle nat parameters and str2int_length_lemma to use proper types */
spec fn pow2_nat(n: nat) -> nat
    decreases n
{
    if n == 0 { 1 } else { 2 * pow2_nat(n - 1) }
}

proof fn str2int_length_lemma(s1: Seq<char>, s2: Seq<char>)
    requires ValidBitString(s1), ValidBitString(s2), s1.len() > s2.len()
    ensures Str2Int(s1) > Str2Int(s2)
{
    let n1 = s1.len() as nat;
    let n2 = s2.len() as nat;
    let min_value_n1 = pow2_nat(n1 - 1);
    let max_value_n2 = pow2_nat(n2) - 1;
    assert(Str2Int(s1) >= min_value_n1);
    assert(Str2Int(s2) <= max_value_n2);
    assert(min_value_n1 > max_value_n2);
}
// </vc-helpers>

// <vc-spec>
exec fn Compare(s1: &[char], s2: &[char]) -> (res: i32)
  requires ValidBitString(s1@),
   ValidBitString(s2@),
  ensures Str2Int(s1@) < Str2Int(s2@) ==> res == -1,
    Str2Int(s1@) == Str2Int(s2@) ==> res == 0,
    Str2Int(s1@) > Str2Int(s2@) ==> res == 1,
  decreases Str2Int(s1@) + Str2Int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Fixed Compare to use proper comparison logic */
{
    let t1 = NormalizeBitString(s1);
    let t2 = NormalizeBitString(s2);
    let n1 = t1.len() as nat;
    let n2 = t2.len() as nat;
    if n1 > n2 {
        return 1;
    } else if n1 < n2 {
        return -1;
    } else {
        let mut i = 0;
        while i < n1 as int
            invariant
                i >= 0,
                i <= n1 as int,
                forall |j: int| 0 <= j && j < i ==> t1@[j] == t2@[j]
            decreases n1 as int - i
        {
            if t1[i] != t2[i] {
                if t1[i] == '1' {
                    return 1;
                } else {
                    return -1;
                }
            }
            i += 1;
        }
        return 0;
    }
}
// </vc-code>

fn main() {}
}


