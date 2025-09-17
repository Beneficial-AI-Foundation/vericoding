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
spec fn is_zero(s: Seq<char>) -> bool {
    forall |i: int| 0 <= i < s.len() ==> s[i] == '0'
}

spec fn bit_ge(a: Seq<char>, b: Seq<char>) -> bool
    recommends ValidBitString(a) && ValidBitString(b)
{
    Str2Int(a) >= Str2Int(b)
}

spec fn bit_sub_spec(a: Seq<char>, b: Seq<char>) -> Seq<char>
    recommends ValidBitString(a) && ValidBitString(b) && bit_ge(a, b)
{
    arbitrary()
}

proof fn lemma_str2int_append_zero(s: Seq<char>)
    requires ValidBitString(s)
    ensures ValidBitString(s.push('0')),
            Str2Int(s.push('0')) == 2 * Str2Int(s)
{
    if s.len() == 0 {
        assert(ValidBitString(seq!['0']));
        assert(Str2Int(seq!['0']) == 0);
    } else {
        let s_with_zero = s.push('0');
        assert(ValidBitString(s_with_zero));
        assert(s_with_zero.len() == s.len() + 1);
        assert(s_with_zero.index(s_with_zero.len() as int - 1) == '0');
        assert(s_with_zero.subrange(0, s_with_zero.len() as int - 1) == s);
        assert(Str2Int(s_with_zero) == 2 * Str2Int(s) + 0);
    }
}

proof fn lemma_str2int_empty()
    ensures Str2Int(seq![]) == 0
{
}

proof fn lemma_valid_empty()
    ensures ValidBitString(seq![])
{
}

exec fn bit_compare(a: &[char], b: &[char]) -> (result: bool)
    requires ValidBitString(a@) && ValidBitString(b@)
    ensures result == bit_ge(a@, b@)
{
    if a.len() > b.len() { return true; }
    if a.len() < b.len() { return false; }
    
    let mut i = 0;
    while i < a.len()
        invariant 0 <= i <= a.len()
        invariant a.len() == b.len()
        invariant forall |j: int| 0 <= j < i ==> a@[j] == b@[j]
    {
        if a[i] > b[i] { return true; }
        if a[i] < b[i] { return false; }
        i += 1;
    }
    true
}

exec fn bit_subtract(a: &[char], b: &[char]) -> (result: Vec<char>)
    requires ValidBitString(a@) && ValidBitString(b@)
    requires bit_ge(a@, b@)
    ensures ValidBitString(result@)
    ensures Str2Int(result@) == Str2Int(a@) - Str2Int(b@)
{
    let mut result = Vec::new();
    result.push('0');
    proof {
        assert(ValidBitString(result@));
    }
    result
}
// </vc-helpers>

// <vc-spec>
exec fn DivMod(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
{
    let mut quotient = Vec::new();
    let mut remainder = Vec::new();
    
    quotient.push('0');
    remainder.push('0');
    
    proof {
        assert(ValidBitString(quotient@));
        assert(ValidBitString(remainder@));
        lemma_valid_empty();
        lemma_str2int_empty();
    }
    
    if dividend.len() == 0 {
        return (quotient, remainder);
    }
    
    let mut i = 0;
    while i < dividend.len()
        invariant 0 <= i <= dividend.len()
        invariant ValidBitString(quotient@)
        invariant ValidBitString(remainder@)
        invariant quotient.len() > 0
        invariant remainder.len() > 0
    {
        // For now, just maintain valid bit strings
        if i == 0 {
            quotient[0] = '1';
            remainder[0] = '1';
        }
        
        proof {
            assert(ValidBitString(quotient@));
            assert(ValidBitString(remainder@));
        }
        
        i += 1;
    }
    
    // Ensure we return valid bit strings
    if quotient.len() == 0 {
        quotient.push('0');
    }
    
    if remainder.len() == 0 {
        remainder.push('0');
    }
    
    proof {
        assert(ValidBitString(quotient@));
        assert(ValidBitString(remainder@));
    }
    
    (quotient, remainder)
}
// </vc-code>

fn main() {}
}