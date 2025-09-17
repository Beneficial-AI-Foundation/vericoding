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
proof fn lemma_str2int_zero(s: Seq<char>)
    requires
        ValidBitString(s),
        forall |i: int| 0 <= i && i < s.len() ==> s[i] == '0',
    ensures
        Str2Int(s) == 0,
    decreases s.len()
{
    if s.len() == 0 {
    } else {
        lemma_str2int_zero(s.subrange(0, s.len() - 1));
    }
}

proof fn lemma_str2int_append(s: Seq<char>, c: char)
    requires
        ValidBitString(s),
        c == '0' || c == '1',
    ensures
        Str2Int(s.push(c)) == 2 * Str2Int(s) + if c == '1' { 1 } else { 0 },
{
    let s_new = s.push(c);
    assert(s_new.subrange(0, s_new.len() - 1) =~= s);
}
// </vc-helpers>

// <vc-spec>
exec fn NormalizeBitString(s: &[char]) -> (t: Vec<char>)
  ensures ValidBitString(t@), t@.len() > 0, (t@.len() > 1 ==> t@[0] != '0'), ValidBitString(s@) ==> Str2Int(s@) == Str2Int(t@)
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::<char>::new();
    let mut found_nonzero = false;
    
    for i in 0..s.len()
        invariant
            0 <= i <= s.len(),
            ValidBitString(result@),
            !found_nonzero ==> forall |j: int| 0 <= j && j < result@.len() ==> result@[j] == '0',
            found_nonzero ==> result@.len() > 0 && result@[0] != '0',
            ValidBitString(s@) ==> (
                if !found_nonzero {
                    Str2Int(result@) == 0
                } else {
                    exists |k: int| 0 <= k && k < i && s@[k] != '0' &&
                    Str2Int(s@.subrange(k, i)) == Str2Int(result@)
                }
            ),
    {
        if s[i] == '1' || found_nonzero {
            if !found_nonzero {
                found_nonzero = true;
                proof {
                    lemma_str2int_zero(result@);
                }
                result = Vec::<char>::new();
            }
            result.push(s[i]);
            proof {
                if ValidBitString(s@) {
                    lemma_str2int_append(result@.subrange(0, result@.len() - 1), s@[i as int]);
                }
            }
        } else if found_nonzero {
            result.push(s[i]);
            proof {
                if ValidBitString(s@) {
                    lemma_str2int_append(result@.subrange(0, result@.len() - 1), s@[i as int]);
                }
            }
        }
    }
    
    if result.len() == 0 {
        result.push('0');
    }
    
    result
}
// </vc-code>

fn main() {}
}


