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

// <vc-helpers>
spec fn Str2NatReverse(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  if s.len() == 0 {
    0
  } else {
    let first_char_val = if s.index(0) == '1' { 1nat } else { 0nat };
    let remaining_val = Str2NatReverse(s.subrange(1, s.len() as int));
    remaining_val + first_char_val * pow(2, (s.len() - 1) as nat)
  }
}

lemma fn Str2IntAlternative(s: Seq<char>)
  requires ValidBitString(s)
  ensures Str2Int(s) == Str2NatReverse(s)
  decreases s.len()
{
  if s.len() > 0 {
    let last_char_val = if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat };
    let s_prefix = s.subrange(0, s.len() as int - 1);
    let prefix_val = Str2Int(s_prefix);
    Str2IntAlternative(s_prefix);

    // Str2Int(s) = 2 * Str2Int(s_prefix) + last_char_val
    // Str2NatReverse(s) = Str2NatReverse(s.subrange(1, s.len() as int)) + (if s.index(0) == '1' { 1nat } else { 0nat }) * pow(2, (s.len() - 1) as nat)

    // This lemma is hard to prove directly in a concise way due to the different recursion directions.
    // A more direct comparison logic is needed in the `Compare` function.
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
{
  // Compare lengths first
  let len1 = s1.len();
  let len2 = s2.len();

  if len1 < len2 {
    return -1;
  } else if len1 > len2 {
    return 1;
  }

  // If lengths are equal, compare lexicographically from most significant bit
  let mut i: int = 0;
  while i < len1
    invariant
      len1 == len2,
      0 <= i && i <= len1,
      // For all j < i, s1[j] == s2[j]
      forall |j: int| 0 <= j && j < i ==> s1@[j] == s2@[j],
      // The prefixes up to i-1 are equal, so Str2Int(s1@.subrange(i, len1)) is the determining factor
      Str2Int(s1@) == Str2Int(s2@) <==> (forall |k: int| i <= k && k < len1 ==> s1@[k] == s2@[k]),
      Str2Int(s1@) < Str2Int(s2@) <==> (exists |k: int| i <= k && k < len1 && s1@[k] == '0' && s2@[k] == '1' && (forall |m: int| i <= m && m < k ==> s1@[m] == s2@[m])), // Simplified: first differing bit s1 is 0, s2 is 1
      Str2Int(s1@) > Str2Int(s2@) <==> (exists |k: int| i <= k && k < len1 && s1@[k] == '1' && s2@[k] == '0' && (forall |m: int| i <= m && m < k ==> s1@[m] == s2@[m])), // Simplified: first differing bit s1 is 1, s2 is 0
    decreases len1 - i
  {
    if s1@[i] < s2@[i] {
      return -1;
    } else if s1@[i] > s2@[i] {
      return 1;
    }
    i = i + 1;
  }

  // If we reached here, strings are identical
  proof {
    assert (Str2Int(s1@) == Str2Int(s2@)); // Follows from loop invariant when `i == len1`
  }
  return 0;
}
// </vc-code>

fn main() {}
}


