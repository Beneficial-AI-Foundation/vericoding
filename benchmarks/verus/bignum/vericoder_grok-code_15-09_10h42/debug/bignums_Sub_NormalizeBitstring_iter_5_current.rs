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
proof fn valid_bitstring_push_bit(seq: Seq<char>, c: char)
requires
    ValidBitString(seq),
    c == '0' || c == '1',
ensures
    ValidBitString(seq.push(c))
{
    assert forall |i: int| 0 <= i < seq.push(c).len() as int ==>
        seq.push(c).index(i) == '0' || seq.push(c).index(i) == '1' by {
            if i < seq.len() as int {
                let _ = ValidBitString(seq);
            } else if i == seq.len() as int {
                let _ = c;
            } else {
                false
            }
        }
}
// </vc-helpers>

// <vc-spec>
exec fn Bignums_Sub_NormalizeBitstring(s: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): added helper calls in proof blocks to prove ValidBitString after pushes */
{
    let mut res: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < s.len() && s[i] == '0'
        invariant
            i <= s@.len(),
            forall |k: int| 0 <= k < i ==> s@[k] == '0',
            ValidBitString(s@),
        decreases s@.len() - i
    {
        i += 1;
    }
    if i == s.len() {
        res.push('0');
        proof {
            valid_bitstring_push_bit(res@, '0');
        }
    } else {
        while i < s.len()
            invariant
                i <= s@.len(),
                ValidBitString(res@),
            decreases s@.len() - i
        {
            res.push(s[i]);
            proof {
                valid_bitstring_push_bit(res@, s[i]);
            }
            i += 1;
        }
    }
    res
}
// </vc-code>

fn main() {}
}
