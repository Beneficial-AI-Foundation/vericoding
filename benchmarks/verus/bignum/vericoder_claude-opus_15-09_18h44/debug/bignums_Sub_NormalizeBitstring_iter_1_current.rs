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
proof fn lemma_valid_bitstring_subrange(s: Seq<char>, start: int, end: int)
    requires
        ValidBitString(s),
        0 <= start <= end <= s.len() as int,
    ensures
        ValidBitString(s.subrange(start, end)),
{
    assert forall |i: int| 0 <= i && i < s.subrange(start, end).len() as int implies
        s.subrange(start, end).index(i) == '0' || s.subrange(start, end).index(i) == '1' by {
        assert(s.subrange(start, end).index(i) == s.index(start + i));
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
    let mut result = Vec::<char>::new();
    let mut i: usize = 0;
    let n = s.len();
    
    // Skip leading zeros
    while i < n && s[i] == '0'
        invariant
            0 <= i <= n,
            ValidBitString(s@),
            forall |j: int| 0 <= j && j < i as int ==> s@.index(j) == '0',
    {
        i = i + 1;
    }
    
    // Copy remaining characters
    while i < n
        invariant
            0 <= i <= n,
            ValidBitString(s@),
            ValidBitString(result@),
            result@.len() == if i == n { 0 } else { (n - i) as int },
            forall |j: int| 0 <= j && j < result@.len() ==> result@.index(j) == s@.index(i as int + j),
    {
        let c = s[i];
        result.push(c);
        i = i + 1;
    }
    
    // If result is empty, add a single '0'
    if result.len() == 0 {
        result.push('0');
    }
    
    result
}
// </vc-code>

fn main() {}
}
