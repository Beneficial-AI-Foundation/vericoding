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

/* helper modified by LLM (iteration 9): fixed syntax in lemma */
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
    /* code modified by LLM (iteration 9): fixed syntax error by using forall assert */
    let mut result = Vec::<char>::new();
    let mut i: usize = 0;
    let n = s.len();
    
    // Skip leading zeros
    while i < n
        invariant
            0 <= i <= n,
            ValidBitString(s@),
            forall |j: int| 0 <= j && j < i as int ==> s@.index(j) == '0',
        decreases n - i
    {
        if i < n && s[i] != '0' {
            break;
        }
        i = i + 1;
    }
    
    // Copy remaining characters
    let start_index = i;
    while i < n
        invariant
            0 <= start_index <= i <= n,
            ValidBitString(s@),
            ValidBitString(result@),
            result@.len() == (i - start_index) as int,
            forall |j: int| 0 <= j && j < result@.len() ==> result@.index(j) == s@.index(start_index as int + j),
        decreases n - i
    {
        assert(i < s@.len());
        let c = s[i];
        assert(s@.index(i as int) == c);
        assert(ValidBitString(s@));
        assert forall |k: int| 0 <= k && k < s@.len() implies (s@.index(k) == '0' || s@.index(k) == '1') by {
            assert(ValidBitString(s@));
        }
        assert(c == '0' || c == '1');
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
