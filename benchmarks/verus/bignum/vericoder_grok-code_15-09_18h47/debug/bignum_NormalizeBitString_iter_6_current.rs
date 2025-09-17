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

// </vc-helpers>

// <vc-spec>
exec fn NormalizeBitString(s: &[char]) -> (t: Vec<char>)
  ensures ValidBitString(t@), t@.len() > 0, (t@.len() > 1 ==> t@[0] != '0'), ValidBitString(s@) ==> Str2Int(s@) == Str2Int(t@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 6): fixed unsupported slice iterator by using index-based loop */
    let mut t: Vec<char> = Vec::with_capacity(s.len());
    for i in 0..s.len() {
        let c = s[i];
        if c == '0' {
            t.push('0');
        } else if c == '1' {
            t.push('1');
        } else {
            t.push('0');
        }
    }
    if t.is_empty() {
        t.push('0');
    }
    let mut pos = None;
    for i in 0..t.len() {
        if t[i] == '1' {
            pos = Some(i);
            break;
        }
    }
    if let Some(p) = pos {
        t = t.split_off(p);
    } else {
        if t.len() > 1 {
            t.truncate(1);
        }
    }
    t
}
// </vc-code>

fn main() {}
}


