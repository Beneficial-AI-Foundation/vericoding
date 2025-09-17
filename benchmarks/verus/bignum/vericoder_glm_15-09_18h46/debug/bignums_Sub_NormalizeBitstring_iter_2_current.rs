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
/* helper modified by LLM (iteration 2): fixed slice indexing by building vector manually */
exec fn normalize_bitstring_helper(s: &[char]) -> (res: Vec<char>)
    requires
        ValidBitString(s@),
    ensures
        ValidBitString(res@),
{
    let mut index = 0;
    let len = s.len();
    while index < len
        invariant
            0 <= index <= len,
            forall |i: int| 0 <= i < index ==> s@[i] == '0',
        decreases
            len - index
    {
        if s[index] == '1' {
            break;
        }
        index += 1;
    }

    if index < len {
        let mut result = Vec::new();
        let mut i = index;
        while i < len {
            result.push(s[i]);
            i += 1;
        }
        result
    } else {
        vec!['0']
    }
}
// </vc-helpers>

// <vc-spec>
exec fn Bignums_Sub_NormalizeBitstring(s: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): using the fixed helper function */
    normalize_bitstring_helper(s)
}
// </vc-code>

fn main() {}
}
