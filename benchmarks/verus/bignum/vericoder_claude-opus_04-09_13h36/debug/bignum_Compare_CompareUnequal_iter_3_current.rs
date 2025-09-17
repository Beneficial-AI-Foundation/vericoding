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
  // All characters must be '0' or '1'.
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
proof fn lemma_str2int_append_bit(s: Seq<char>, bit: char)
    requires
        ValidBitString(s),
        bit == '0' || bit == '1',
    ensures
        ValidBitString(s.push(bit)),
        Str2Int(s.push(bit)) == 2 * Str2Int(s) + (if bit == '1' { 1nat } else { 0nat }),
    decreases s.len(),
{
    let s_new = s.push(bit);
    assert(s_new.len() == s.len() + 1);
    assert(s_new.subrange(0, s_new.len() as int - 1) =~= s);
    assert(s_new.index(s_new.len() as int - 1) == bit);
}

proof fn lemma_str2int_leading_zeros(s: Seq<char>, k: int)
    requires
        ValidBitString(s),
        0 <= k <= s.len(),
        forall|j: int| 0 <= j && j < k ==> s[j] == '0',
    ensures
        Str2Int(s.subrange(0, k)) == 0nat,
        k < s.len() ==> Str2Int(s) == Str2Int(s.subrange(k, s.len() as int)),
    decreases k,
{
    if k == 0 {
        assert(s.subrange(0, 0).len() == 0);
    } else {
        lemma_str2int_leading_zeros(s.subrange(1, s.len() as int), k - 1);
        assert(s.subrange(0, k) =~= seq![s[0]].add(s.subrange(1, k)));
        if k == s.len() {
            assert(Str2Int(s.subrange(0, k)) == Str2Int(s));
        }
    }
}

proof fn lemma_normalize_preserves_value(s: Seq<char>)
    requires ValidBitString(s),
    ensures 
        s.len() == 0 ==> Str2Int(s) == 0nat,
        s.len() > 0 && (forall|j: int| 0 <= j && j < s.len() ==> s[j] == '0') ==> Str2Int(s) == 0nat,
{
    if s.len() > 0 && (forall|j: int| 0 <= j && j < s.len() ==> s[j] == '0') {
        lemma_str2int_leading_zeros(s, s.len() as int);
    }
}
// </vc-helpers>

// <vc-spec>
exec fn NormalizeBitString(s: &[char]) -> (t: Vec<char>)
  ensures ValidBitString(t@),
   t@.len() > 0,
   t@.len() > 1 ==> t@[0] != '0',
   ValidBitString(s@) ==> Str2Int(s@) == Str2Int(t@)
// </vc-spec>
// <vc-code>
{
    let mut result = Vec::<char>::new();
    let mut found_one = false;
    
    for i in 0..s.len()
        invariant
            ValidBitString(result@),
            found_one ==> (result@.len() > 0 && result@[0] == '1'),
            !found_one ==> forall|j: int| 0 <= j && j < result@.len() ==> result@[j] == '0',
            ValidBitString(s@.subrange(0, i as int)) ==> 
                Str2Int(s@.subrange(0, i as int)) == (if found_one { Str2Int(result@) } else { 0nat }),
    {
        if s[i] == '1' {
            if !found_one {
                found_one = true;
                result = Vec::<char>::new();
                proof {
                    lemma_str2int_append_bit(result@, '1');
                }
                result.push('1');
            } else {
                proof {
                    lemma_str2int_append_bit(result@, '1');
                }
                result.push('1');
            }
        } else if s[i] == '0' {
            if found_one {
                proof {
                    lemma_str2int_append_bit(result@, '0');
                }
                result.push('0');
            }
        }
    }
    
    if result.len() == 0 {
        result.push('0');
    }
    
    proof {
        if ValidBitString(s@) {
            lemma_normalize_preserves_value(s@);
            if !found_one {
                assert(forall|j: int| 0 <= j && j < s@.len() ==> s@[j] == '0' || s@[j] != '0' && s@[j] != '1');
                assert(Str2Int(s@) == 0nat);
                assert(result@.len() == 1);
                assert(result@[0] == '0');
                assert(Str2Int(result@) == 0nat);
            }
        }
    }
    
    result
}
// </vc-code>

fn main() {}
}