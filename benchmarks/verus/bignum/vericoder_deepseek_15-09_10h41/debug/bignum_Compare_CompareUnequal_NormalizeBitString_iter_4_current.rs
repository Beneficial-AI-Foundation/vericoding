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
/* code modified by LLM (iteration 4): Fixed type conversion issues and logic */
{
    let mut result = Vec::new();
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i && i <= s.len(),
            ValidBitString(result@),
            s@.len() > 0 ==> (result@.len() > 0 || i < s.len()),
            (forall |j: int| 0 <= j && j < i ==> s[j] == '0') ==> result@.len() == 0,
            Str2Int(s@) == Str2Int(result@)
        decreases s.len() - i
    {
        if s[i] != '0' {
            result.extend_from_slice(&s[i..s.len()]);
            break;
        }
        i += 1;
    }
    if result.is_empty() {
        result.push('0');
    }
    result
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
/* code modified by LLM (iteration 4): Fixed assumption about s1 longer than s2 */
{
    let n1 = s1.len();
    let n2 = s2.len();
    
    if n1 > n2 {
        1
    } else if n1 < n2 {
        -1
    } else {
        let mut i = 0;
        while i < n1
            invariant
                0 <= i && i <= n1,
                forall |j: int| 0 <= j && j < i ==> s1[j] == s2[j],
                Str2Int(s1@.subrange(0, i)) == Str2Int(s2@.subrange(0, i))
            decreases n1 - i
        {
            if s1[i] != s2[i] {
                if s1[i] == '1' {
                    break 1;
                } else {
                    break -1;
                }
            }
            i += 1;
        }
        0
    }
}
// </vc-code>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Fixed pow2 parameter types and proofs */
use vstd::arithmetic::power2::pow2;

proof fn str2int_higher_bit_lemma(s1: Seq<char>, s2: Seq<char>)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
        s1.len() > s2.len(),
        s1.len() > 0,
        s2.len() > 0,
        (s1.len() > 1 ==> s1[0] != '0'),
        (s2.len() > 1 ==> s2[0] != '0')
    ensures
        Str2Int(s1) > Str2Int(s2)
{
    str2int_monotonic_lemma(s1, s2);
}

proof fn str2int_length_lemma(s: Seq<char>, n: nat)
    requires
        ValidBitString(s),
        s.len() == n,
        s.len() > 0,
        (s.len() > 1 ==> s[0] != '0')
    ensures
        Str2Int(s) >= pow2((n - 1) as nat)
{
    pow2_positive_lemma((n - 1) as nat);
}

proof fn pow2_positive_lemma(n: nat)
    ensures
        pow2(n) > 0
{
}

proof fn str2int_monotonic_lemma(s1: Seq<char>, s2: Seq<char>)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
        s1.len() > s2.len()
    ensures
        Str2Int(s1) >= pow2((s1.len() - 1) as nat),
        Str2Int(s2) <= pow2(s2.len() as nat) - 1,
        pow2((s1.len() - 1) as nat) > pow2(s2.len() as nat) - 1
{
    pow2_positive_lemma(s2.len() as nat);
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
/* code modified by LLM (iteration 4): Fixed type conversion and added proof block */
{
    let t1 = NormalizeBitString(s1);
    let t2 = NormalizeBitString(s2);
    proof {
        assert(ValidBitString(t1@));
        assert(ValidBitString(t2@));
        assert(t1@.len() > 0);
        assert(t2@.len() > 0);
        assert(Str2Int(s1@) == Str2Int(t1@));
        assert(Str2Int(s2@) == Str2Int(t2@));
    }
    CompareUnequal(&t1, &t2)
}
// </vc-code>

fn main() {}
}


