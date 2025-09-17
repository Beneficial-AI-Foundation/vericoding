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
spec fn TrimLeadingZeros(s: Seq<char>) -> Seq<char>
  requires
    ValidBitString(s),
  ensures
    ValidBitString(TrimLeadingZeros(s)),
    (s.len() == 0 ==> TrimLeadingZeros(s).len() == 0),
    (s.len() > 0 && s.index(0) == '0' ==> TrimLeadingZeros(s).len() < s.len()),
    (s.len() > 0 && s.index(0) == '1' ==> TrimLeadingZeros(s) == s),
    (s.len() > 0 && s.index(0) == '0' && forall |i: int| 0 <= i && i < s.len() ==> s.index(i) == '0' ==> TrimLeadingZeros(s) == Seq::singleton('0')),
    (s.len() > 0 ==> (TrimLeadingZeros(s).len() == 1 ==> TrimLeadingZeros(s).index(0) == '0') || TrimLeadingZeros(s).index(0) == '1'),
    Str2Int(s) == Str2Int(TrimLeadingZeros(s)),
  decreases s.len()
{
  if s.len() == 0 {
    s
  } else if s.len() == 1 {
    s
  } else if s.index(0) == '1' {
    s
  } else {
    let trimmed = TrimLeadingZeros(s.subrange(1, s.len() as int));
    if trimmed.len() == 0 {
      Seq::singleton('0')
    } else {
      trimmed
    }
  }
}
// </vc-helpers>

// <vc-spec>
exec fn NormalizeBitString(s: &[char]) -> (t: Vec<char>)
  ensures ValidBitString(t@), t@.len() > 0, (t@.len() > 1 ==> t@[0] != '0'), ValidBitString(s@) ==> Str2Int(s@) == Str2Int(t@)
// </vc-spec>
// <vc-code>
{
  let mut i: int = 0;
  while i < s.len() && s[i] == '0'
    invariant
      0 <= i,
      i <= s.len(),
      ValidBitString(s@),
  {
    i = i + 1;
  }

  let t: Vec<char>;
  if i == s.len() {
    // All zeros, or empty string. Return "0"
    t = vec!['0'];
  } else {
    // There's at least one '1' or we stopped at the first non-'0'
    let mut result_vec = Vec::<char>::new();
    let mut j = i;
    while j < s.len()
      invariant
        i <= j,
        j <= s.len(),
        ValidBitString(s@),
        result_vec@ == s@.subrange(i, j as int),
    {
      result_vec.push(s[j]);
      j = j + 1;
    }
    t = result_vec;
  }
  t
}
// </vc-code>

fn main() {}
}


