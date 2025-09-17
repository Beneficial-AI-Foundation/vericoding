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
/* code modified by LLM (iteration 7): Fixed compilation error by avoiding Vec::is_empty method */
{
    let mut t = Vec::new();
    let mut i = 0;
    let mut found_one = false;
    while i < s.len()
        invariant
            i >= 0,
            i <= s.len()
    {
        if s[i] == '1' {
            t.push('1');
            found_one = true;
            i += 1;
        } else if s[i] == '0' {
            if found_one {
                t.push('0');
            }
            i += 1;
        } else {
            proof { assert(false); }
        }
    }
    if t.len() == 0 {
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
/* code modified by LLM (iteration 7): Fixed compilation error by using proper length comparison */
{
    let n1 = s1.len();
    let n2 = s2.len();
    if n1 > n2 {
        return 1;
    } else {
        let mut i = 0;
        while i < n2
            invariant
                i >= 0,
                i <= n2
        {
            if i >= n1 {
                return -1;
            }
            if s1[i] != s2[i] {
                if s1[i] == '1' {
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

// <vc-helpers>
/* helper modified by LLM (iteration 7): Fixed compilation errors by using proper nat types and removing int conversions */
proof fn str2int_length_lemma(s1: Seq<char>, s2: Seq<char>)
    requires ValidBitString(s1), ValidBitString(s2), s1.len() > s2.len()
    ensures Str2Int(s1) > Str2Int(s2)
{
    let max_bit_value = pow2_nat((s1.len() - 1) as nat);
    assert(Str2Int(s1) >= max_bit_value);
    let max_s2_value = (pow2_nat(s2.len() as nat) - 1) as nat;
    assert(max_bit_value > max_s2_value);
}

spec fn pow2_nat(n: nat) -> nat {
    if n == 0 { 1 } else { 2 * pow2_nat((n - 1) as nat) }
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
/* code modified by LLM (iteration 7): Fixed compilation error by avoiding Vec::is_empty method */
{
    let t1 = NormalizeBitString(s1);
    let t2 = NormalizeBitString(s2);
    let n1 = t1.len();
    let n2 = t2.len();
    if n1 > n2 {
        return 1;
    } else if n1 < n2 {
        return -1;
    } else {
        let mut i = 0;
        while i < n1
            invariant
                i >= 0,
                i <= n1
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


