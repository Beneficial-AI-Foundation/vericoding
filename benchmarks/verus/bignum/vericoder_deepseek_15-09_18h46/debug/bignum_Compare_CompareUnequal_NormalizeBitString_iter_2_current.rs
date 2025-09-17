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
/* code modified by LLM (iteration 2): NormalizeBitString implementation */
{
    let mut t = Vec::new();
    let mut i = 0;
    while i < s.len()
        invariant
            ValidBitString(t@),
            i >= 0,
            i <= s.len(),
            ValidBitString(s@) ==> Str2Int(s@) == Str2Int(t@)
        decreases s.len() - i
    {
        t.push(s[i]);
        i += 1;
    }
    let mut j = 0;
    while j < t.len() && t[j] == '0'
        invariant
            ValidBitString(t@),
            j >= 0,
            j <= t.len(),
            ValidBitString(s@) ==> Str2Int(s@) == Str2Int(t@)
        decreases t.len() - j
    {
        j += 1;
    }
    if j == t.len() {
        t.truncate(1);
        t[0] = '0';
    } else {
        t = t.split_off(j);
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
/* code modified by LLM (iteration 2): CompareUnequal implementation */
{
    let n1 = s1.len();
    let n2 = s2.len();
    proof {
        lemma_str2int_monotonic(s1@, s2@);
    }
    1
}
// </vc-code>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Fix lemma_str2int_monotonic parameter types and add proper annotations */
fn compare_unequal_helper(s1: &[char], s2: &[char]) -> (res: i32)
    requires
        ValidBitString(s1@),
        ValidBitString(s2@),
        s1@.len() > 0,
        s2@.len() > 0,
        s1@.len() > s2@.len()
    ensures
        res == 1
{
    let n1 = s1.len();
    let n2 = s2.len();
    proof {
        lemma_str2int_monotonic(s1@, s2@);
    }
    1
}

proof fn lemma_str2int_monotonic(s1: Seq<char>, s2: Seq<char>)
    requires
        ValidBitString(s1),
        ValidBitString(s2),
        s1.len() > s2.len()
    ensures
        Str2Int(s1) > Str2Int(s2)
{
    if s2.len() == 0 {
        assert(Str2Int(s2) == 0);
        assert(Str2Int(s1) >= 1);
    } else {
        let s1_prefix = s1.subrange(0, s1.len() as int - 1);
        let s2_prefix = s2.subrange(0, s2.len() as int - 1);
        lemma_str2int_monotonic(s1_prefix, s2_prefix);
        assert(Str2Int(s1) == 2 * Str2Int(s1_prefix) + (if s1[s1.len() as int - 1] == '1' { 1nat } else { 0nat }));
        assert(Str2Int(s2) == 2 * Str2Int(s2_prefix) + (if s2[s2.len() as int - 1] == '1' { 1nat } else { 0nat }));
        assert(Str2Int(s1) >= 2 * Str2Int(s1_prefix));
        assert(Str2Int(s2) <= 2 * Str2Int(s2_prefix) + 1);
        assert(2 * Str2Int(s1_prefix) >= 2 * Str2Int(s2_prefix) + 2);
    }
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
/* code modified by LLM (iteration 2): Compare implementation using normalized strings */
{
    let s1_norm = NormalizeBitString(s1);
    let s2_norm = NormalizeBitString(s2);
    if s1_norm.len() > s2_norm.len() {
        return 1;
    } else if s1_norm.len() < s2_norm.len() {
        return -1;
    } else {
        CompareUnequal(s1_norm.as_slice(), s2_norm.as_slice())
    }
}
// </vc-code>

fn main() {}
}


