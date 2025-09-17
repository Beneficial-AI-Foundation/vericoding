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
/* helper modified by LLM (iteration 5): Fixed subrange calls and types */
spec fn count_nonzero(s: Seq<char>) -> nat
    recommends ValidBitString(s)
    decreases s.len()
{
    if s.len() == 0 {
        0
    } else if s.index(0) == '1' {
        1 + count_nonzero(s.subrange(1, s.len() as int))
    } else {
        count_nonzero(s.subrange(1, s.len() as int))
    }
}

proof fn lemma_str2int_leading_zeros(s: Seq<char>, num_zeros: int)
    requires
        ValidBitString(s),
        0 <= num_zeros && num_zeros <= s.len() as int,
        forall |j: int| 0 <= j && j < num_zeros ==> s[j] == '0'
    ensures
        Str2Int(s) == Str2Int(s.subrange(num_zeros, s.len() as int))
    decreases num_zeros
{
    if num_zeros > 0 {
        assert(s.index(0) == '0');
        assert(s == Seq::new(0, |i: int| s.index(i)));
        lemma_str2int_leading_zeros(s.subrange(1, s.len() as int), num_zeros - 1);
    }
}

fn strip_leading_zeros(s: Vec<char>) -> (t: Vec<char>)
    ensures
        t@ == s@.subrange(s@.len() as int - count_nonzero(s@) as int, s@.len() as int),
        (t@.len() > 0 ==> t@[0] == '1'),
        ValidBitString(s@) ==> Str2Int(s@) == Str2Int(t@),
        ValidBitString(s@) ==> ValidBitString(t@)
    decreases s@.len()
{
    proof {
        lemma_str2int_leading_zeros(s@, s@.len() as int - count_nonzero(s@) as int);
    }
    let mut i = 0;
    while i < s.len() && s[i] == '0'
        invariant
            0 <= i && i <= s@.len() as int,
            forall |j: int| 0 <= j && j < i ==> s@[j] == '0',
            i <= s@.len() as int - count_nonzero(s@) as int
        decreases s@.len() as int - i
    {
        i = i + 1;
    }
    s.subslice(i as usize, s.len())
}
// </vc-helpers>

// <vc-spec>
exec fn NormalizeBitString(s: &[char]) -> (t: Vec<char>)
  ensures ValidBitString(t@), t@.len() > 0, (t@.len() > 1 ==> t@[0] != '0'), ValidBitString(s@) ==> Str2Int(s@) == Str2Int(t@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed Vec construction and validation */
{
    let mut result: Vec<char> = Vec::new();
    if ValidBitString(s@) {
        let s_vec = s.to_vec();
        let stripped = strip_leading_zeros(s_vec);
        if stripped.is_empty() {
            result.push('0');
        } else {
            result = stripped;
        }
    } else {
        result.push('0');
    }
    proof {
        if result@.len() > 1 {
            assert(result@[0] != '0');
        }
        assert_by(ValidBitString(result@), {
            assert(forall |i: int| 0 <= i && i < result@.len() as int ==> 
                result@[i] == '0' || result@[i] == '1');
        });
        if ValidBitString(s@) {
            assert(Str2Int(s@) == Str2Int(result@));
        }
    }
    result
}
// </vc-code>

fn main() {}
}


