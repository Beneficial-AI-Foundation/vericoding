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
spec fn Add(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  recommends ValidBitString(s1), ValidBitString(s2)
  ensures ValidBitString(res), Str2Int(res) == Str2Int(s1) + Str2Int(s2)
{
  if s1.len() == 0 {
    s2
  } else if s2.len() == 0 {
    s1
  } else {
    let last1 = s1.index(s1.len() as int - 1);
    let last2 = s2.index(s2.len() as int - 1);
    let bit1 = if last1 == '1' { 1nat } else { 0nat };
    let bit2 = if last2 == '1' { 1nat } else { 0nat };
    let sum_bits = bit1 + bit2;
    let rest = Add(s1.subrange(0, s1.len() as int - 1), s2.subrange(0, s2.len() as int - 1));
    let carry = if sum_bits >= 2 {
        Add(rest, seq!['1'])
    } else {
        rest
    };
    let last_char = if sum_bits % 2 == 1 { '1' } else { '0' };
    carry.push(last_char)
  }
}

spec fn ShiftLeft(s: Seq<char>, n: nat) -> (res: Seq<char>)
  recommends ValidBitString(s)
  ensures ValidBitString(res), Str2Int(res) == Str2Int(s) * (pow2(n))
{
  if n == 0 {
    s
  } else {
    let s_shifted = ShiftLeft(s, n - 1);
    s_shifted.push('0')
  }
}

spec fn pow2(n: nat) -> nat
  ensures pow2(0) == 1,
  forall |m: nat| pow2(m + 1) == 2 * pow2(m)
{
  if n == 0 {
    1
  } else {
    2 * pow2(n - 1)
  }
}

proof fn Str2Int_shift_left(s: Seq<char>, n: nat)
  recommends
    ValidBitString(s),
  ensures
    Str2Int(ShiftLeft(s, n)) == Str2Int(s) * (pow2(n))
{
  if n == 0 {
  } else {
    let s_shifted = ShiftLeft(s, n - 1);
    Str2Int_shift_left(s, n - 1);
    assert(ShiftLeft(s, n) == ShiftLeft(s_shifted, 1));
    assert(ShiftLeft(s_shifted, 1) == s_shifted.push('0'));
    assert(Str2Int(s_shifted.push('0')) == 2 * Str2Int(s_shifted));
  }
}

proof fn Str2Int_add(s1: Seq<char>, s2: Seq<char>)
  recommends
    ValidBitString(s1), ValidBitString(s2),
  ensures
    Str2Int(Add(s1, s2)) == Str2Int(s1) + Str2Int(s2)
{
  if s1.len() == 0 {
  } else if s2.len() == 0 {
  } else {
    let last1 = s1.index(s1.len() as int - 1);
    let last2 = s2.index(s2.len() as int - 1);
    let bit1 = if last1 == '1' { 1nat } else { 0nat };
    let bit2 = if last2 == '1' { 1nat } else { 0nat };
    let sum_bits = bit1 + bit2;
    let rest = Add(s1.subrange(0, s1.len() as int - 1), s2.subrange(0, s2.len() as int - 1));
    Str2Int_add(s1.subrange(0, s1.len() as int - 1), s2.subrange(0, s2.len() as int - 1));
    if sum_bits >= 2 {
        Str2Int_add(rest, seq!['1']);
        assert(Str2Int(Add(rest, seq!['1'])) == Str2Int(rest) + 1);
        assert(Add(s1, s2) == Add(rest, seq!['1']).push(if sum_bits % 2 == 1 { '1' } else { '0' }));
    } else {
        assert(Add(s1, s2) == rest.push(if sum_bits % 2 == 1 { '1' } else { '0' }));
    }
  }
}
// </vc-helpers>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
    if s1.is_empty() || s2.is_empty() {
        return Vec::<char>::new();
    }
    
    let mut result = Vec::with_capacity(s1.len() + s2.len());
    result.push('0');
    
    let mut i = 0;
    while i < s2.len()
        invariant
            i <= s2.len(),
            ValidBitString(result@),
            Str2Int(result@) == Str2Int(s1@) * Str2Int(s2@.subrange(0, i as int)),
        decreases
            s2.len() - i,
    {
        let bit_char = s2[s2.len() - 1 - i];
        let bit_val = if bit_char == '1' { 1 } else { 0 };
        
        let mut shifted;
        if bit_val == 1 {
            shifted = Vec::new();
            for j in 0..s1.len() {
                shifted.push(s1[j]);
            }
            for _ in 0..i {
                shifted.push('0');
            }
        } else {
            shifted = Vec::new();
            shifted.push('0');
        }
        
        let mut new_result = Vec::new();
        let carry;
        {
            proof {
                Str2Int_add(result@, shifted@);
            }
        }
        
        let mut sum_result = Add(result@, shifted@);
        for j in 0..sum_result.len() {
            new_result.push(sum_result.index(j as int));
        }
        
        result = new_result;
        i += 1;
    }
    
    return result;
}
// </vc-code>

fn main() {}
}


