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
proof fn Str2Int_zero_suffix_lemma(s1: Seq<char>, s2: Seq<char>)
    requires ValidBitString(s1 + s2),
    ensures Str2Int(s1 + s2) == Str2Int(s1) + Str2Int(s2) * pow2(s1.len() as nat)
    decreases s1.len()
{
    if s1.is_empty() {
        assert(s1 + s2 == s2);
        assert(Str2Int(s1) == 0);
        assert(pow2(0) == 1);
    } else {
        let last_char = s1[s1.len() as int - 1];
        let prefix = s1.subrange(0, s1.len() as int - 1);
        assert(s1 == prefix + Seq::new(1, |i| last_char));
        Str2Int_zero_suffix_lemma(prefix, s2);
        let bit_value = if last_char == '1' { 1nat } else { 0nat };
        assert(Str2Int(s1 + s2) == 2 * Str2Int(prefix + s2) + bit_value);
        assert(Str2Int(s1 + s2) == 2 * (Str2Int(prefix) + Str2Int(s2) * pow2(prefix.len() as nat)) + bit_value);
        assert(Str2Int(s1 + s2) == (2 * Str2Int(prefix) + bit_value) + Str2Int(s2) * pow2(prefix.len() as nat + 1));
        assert(Str2Int(s1) == 2 * Str2Int(prefix) + bit_value);
        assert(prefix.len() as nat + 1 == s1.len() as nat);
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
    let mut normalized = Vec::new();
    let mut leading_zeroes = true;
    
    proof {
        let s_seq = s@;
        let original_value = Str2Int(s_seq);
        let mut normalized_value = 0nat;
        let mut normalized_seq = Seq::<char>::empty();
        
        for i in 0..s.len() {
            if s_seq[i as int] == '1' {
                leading_zeroes = false;
                normalized_seq = normalized_seq.push('1');
                normalized_value = 2 * normalized_value + 1;
            } else if !leading_zeroes {
                normalized_seq = normalized_seq.push('0');
                normalized_value = 2 * normalized_value;
            } else {
                normalized_value = 0;
            }
        }
        
        if normalized_seq.is_empty() {
            normalized_seq = normalized_seq.push('0');
            normalized_value = 0;
        }
        
        Str2Int_zero_suffix_lemma(normalized_seq, s_seq);
        assert(Str2Int(s_seq) == Str2Int(normalized_seq) + normalized_value * pow2(normalized_seq.len() as nat));
        assert(normalized_value == 0);
        assert(Str2Int(s_seq) == Str2Int(normalized_seq));
        assert(ValidBitString(normalized_seq));
    }
    
    for i in 0..s.len() {
        if s[i] == '1' {
            leading_zeroes = false;
            normalized.push('1');
        } else if !leading_zeroes {
            normalized.push('0');
        }
    }
    
    if normalized.is_empty() {
        normalized.push('0');
    }
    
    normalized
}
// </vc-code>

fn main() {}
}
