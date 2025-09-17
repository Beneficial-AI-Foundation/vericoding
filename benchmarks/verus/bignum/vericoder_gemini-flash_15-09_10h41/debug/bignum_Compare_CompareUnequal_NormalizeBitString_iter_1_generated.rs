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
{
  let mut s_vec = s.to_vec();
  if s_vec.len() == 0 {
    s_vec.push('0');
    return s_vec;
  }

  let mut first_one_idx: int = -1;
  let mut i: int = 0;
  while i < s_vec.len() as int
    invariant
      0 <= i,
      i <= s_vec.len() as int,
      first_one_idx < i,
      forall|j: int| 0 <= j < i ==> s_vec@[j] == '0' ==> first_one_idx == -1,
      forall|j: int| 0 <= j < i ==> s_vec@[j] == '1' ==> first_one_idx >= 0 && j >= first_one_idx && s_vec@[first_one_idx] == '1'
    decreases s_vec.len() - i
  {
    if s_vec@[i] == '1' {
      first_one_idx = i;
      break;
    }
    i = i + 1;
  }

  if first_one_idx == -1 {
    return vec!['0'];
  }

  let mut result = Vec::with_capacity(s_vec.len() - first_one_idx);
  let mut j = first_one_idx;
  while j < s_vec.len() as int
    invariant
      first_one_idx <= j,
      j <= s_vec.len() as int,
      result.len() == j - first_one_idx,
      forall|k: int| 0 <= k < result.len() ==> result@[k] == s_vec@[first_one_idx + k]
    decreases s_vec.len() - j
  {
    result.push(s_vec@[j]);
    j = j + 1;
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
{
  let s1_len = s1.len();
  let s2_len = s2.len();

  if s1_len > s2_len {
    return 1;
  } else if s1_len < s2_len {
    return -1;
  } else {
    let mut i: int = 0;
    while i < s1_len as int
      invariant
        0 <= i,
        i <= s1_len as int,
        forall|j: int| 0 <= j < i ==> s1@[j] == s2@[j]
      decreases s1_len - i
    {
      if s1@[i] > s2@[i] {
        return 1;
      } else if s1@[i] < s2@[i] {
        return -1;
      }
      i = i + 1;
    }
    return 0;
  }
}
// </vc-code>

// <vc-helpers>
proof fn lemma_Str2Int_lits(s_prefix: Seq<char>, last_char: char)
  requires
    ValidBitString(s_prefix),
    last_char == '0' || last_char == '1'
  ensures
    ValidBitString(s_prefix + Seq::singleton(last_char))
{
  if s_prefix.len() > 0 {
    assert forall|i: int| 0 <= i < (s_prefix + Seq::singleton(last_char)).len() implies
      ((s_prefix + Seq::singleton(last_char)).index(i) == '0' || (s_prefix + Seq::singleton(last_char)).index(i) == '1') by {
      if i < s_prefix.len() {
        assert(s_prefix.index(i) == '0' || s_prefix.index(i) == '1');
      } else {
        assert(i == s_prefix.len());
        assert((s_prefix + Seq::singleton(last_char)).index(i) == last_char);
        assert(last_char == '0' || last_char == '1');
      }
    }
  }
}

proof fn lemma_Str2Int_append(s: Seq<char>, c: char)
  requires ValidBitString(s),
   (c == '0' || c == '1')
  ensures Str2Int(s + Seq::singleton(c)) == 2 * Str2Int(s) + (if c == '1' { 1nat } else { 0nat })
{
  if s.len() == 0 {
    assert(Str2Int(Seq::singleton(c)) == (if c == '1' { 1nat } else { 0nat }));
    assert(2 * Str2Int(s) == 0);
  }
}

proof fn lemma_Str2Int_zero_prefix(s: Seq<char>, k: nat)
  requires
    k > 0,
    ValidBitString(s),
    forall|i: int| 0 <= i < k ==> s.index(i) == '0'
  ensures
    Str2Int(s) == Str2Int(s.subrange(k as int, s.len() as int))
{
  if k == 1 {
    if s.len() > 0 {
      assert(s.index(0) == '0');
      if s.len() == 1 {
        assert(Str2Int(s) == 0);
        assert(Str2Int(s.subrange(1, 1)) == Str2Int(Seq::<char>::empty()) == 0);
      } else {
        let s_prime = s.subrange(1, s.len() as int);
        assert(forall|j: int| 0 <= j < s_prime.len() ==> s_prime.index(j) == s.index((1 + j) as int));
        assert(Str2Int(s) == 2 * Str2Int(s.subrange(0, (s.len() - 1) as int)) + (if s.index((s.len() - 1) as int) == '1' { 1nat } else { 0nat }));
        assert(Str2Int(s) == 2 * (2 * Str2Int(s.subrange(0, (s.len() - 2) as int)) + (if s.index((s.len() - 2) as int) == '1' { 1nat } else { 0nat })) + (if s.index((s.len() - 1) as int) == '1' { 1nat } else { 0nat }));
      }
    }
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
  let normalized_s1 = NormalizeBitString(s1);
  let normalized_s2 = NormalizeBitString(s2);

  let s1_len = normalized_s1.len();
  let s2_len = normalized_s2.len();

  if s1_len > s2_len {
    return 1;
  } else if s1_len < s2_len {
    return -1;
  } else {
    let mut i: int = 0;
    while i < s1_len as int
      invariant
        0 <= i,
        i <= s1_len as int,
        normalized_s1.len() == s1_len,
        normalized_s2.len() == s2_len,
        s1_len == s2_len,
        forall|j: int| 0 <= j < i ==> normalized_s1@[j] == normalized_s2@[j]
      decreases s1_len - i
    {
      if normalized_s1@[i] > normalized_s2@[i] {
        return 1;
      } else if normalized_s1@[i] < normalized_s2@[i] {
        return -1;
      }
      i = i + 1;
    }
    return 0;
  }
}
// </vc-code>

fn main() {}
}


