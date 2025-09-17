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

/* helper modified by LLM (iteration 3): added lemma to ensure valid char is pushed */
proof fn lemma_push_valid_char(v: Seq<char>, c: char)
    requires
        ValidBitString(v),
        c == '0' || c == '1',
    ensures
        ValidBitString(v.push(c)),
{
    assert forall |i: int| 0 <= i && i < v.push(c).len() implies
        v.push(c).index(i) == '0' || v.push(c).index(i) == '1' by {
        if i < v.len() {
            assert(v.push(c).index(i) == v.index(i));
        } else {
            assert(v.push(c).index(i) == c);
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
{
    /* code modified by LLM (iteration 3): fixed loop invariants and bounds checking */
    let mut result = Vec::<char>::new();
    let mut i: usize = 0;
    let n = s.len();
    
    // Skip leading zeros
    while i < n
        invariant
            0 <= i <= n,
            ValidBitString(s@),
            forall |j: int| 0 <= j && j < i as int ==> s@[j] == '0' || i == 0,
        decreases n - i
    {
        if s[i] != '0' {
            break;
        }
        i = i + 1;
    }
    
    // Copy remaining characters
    while i < n
        invariant
            0 <= i <= n,
            ValidBitString(s@),
            ValidBitString(result@),
            result@.len() == if i == 0 { 0 } else { (i - (i - result.len())) as int },
            forall |j: int| 0 <= j && j < result@.len() ==> result@[j] == s@[(i - result.len()) as int + j],
        decreases n - i
    {
        let c = s[i];
        proof {
            lemma_push_valid_char(result@, c);
        }
        result.push(c);
        i = i + 1;
    }
    
    // If result is empty, add a single '0'
    if result.len() == 0 {
        proof {
            lemma_push_valid_char(result@, '0');
        }
        result.push('0');
    }
    
    result
}
// </vc-code>

fn main() {}
}
