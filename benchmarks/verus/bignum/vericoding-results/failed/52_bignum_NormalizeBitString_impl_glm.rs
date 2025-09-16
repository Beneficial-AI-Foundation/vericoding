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
exec fn is_valid_bitstring(s: &[char]) -> bool {
    let mut i = 0;
    while i < s.len()
        invariant
            0 <= i <= s.len(),
            forall |j: int| 0 <= j && j < i as int ==> s[j as usize] == '0' || s[j as usize] == '1'
        decreases s.len() - i
    {
        if s[i] != '0' && s[i] != '1' {
            return false;
        }
        i += 1;
    }
    true
}
// </vc-helpers>

// <vc-spec>
exec fn NormalizeBitString(s: &[char]) -> (t: Vec<char>)
  ensures ValidBitString(t@), t@.len() > 0, (t@.len() > 1 ==> t@[0] != '0'), ValidBitString(s@) ==> Str2Int(s@) == Str2Int(t@)
// </vc-spec>
// <vc-code>
{
    if s.is_empty() {
        return vec!['0'];
    }
    if !is_valid_bitstring(s) {
        return vec!['0'];
    }
    let mut start_index = 0;
    while start_index < s.len() && s[start_index] == '0'
        invariant
            start_index <= s.len()
        decreases s.len() - start_index
    {
        start_index += 1;
    }
    if start_index == s.len() {
        return vec!['0'];
    } else {
        return s[start_index..].to_vec();
    }
}
// </vc-code>

fn main() {}
}


