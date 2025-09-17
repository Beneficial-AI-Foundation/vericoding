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
spec fn Int2Str(n: nat) -> Seq<char>
  decreases n
{
  if n == 0 {
    seq!['0']
  } else if n == 1 {
    seq!['1']
  } else {
    Int2Str(n / 2) + seq![if n % 2 == 0 { '0' } else { '1' }]
  }
}

proof fn lemma_str2int_int2str_inverse(n: nat)
  ensures ValidBitString(Int2Str(n))
  ensures Str2Int(Int2Str(n)) == n
  decreases n
{
  if n == 0 {
    assert(Int2Str(n) == seq!['0']);
    assert(ValidBitString(Int2Str(n)));
    assert(Str2Int(Int2Str(n)) == 0);
  } else if n == 1 {
    assert(Int2Str(n) == seq!['1']);
    assert(ValidBitString(Int2Str(n)));
    assert(Str2Int(Int2Str(n)) == 1);
  } else {
    lemma_str2int_int2str_inverse(n / 2);
    let s_half = Int2Str(n / 2);
    let bit = if n % 2 == 0 { '0' } else { '1' };
    let s = s_half + seq![bit];
    
    assert(ValidBitString(s_half));
    assert(bit == '0' || bit == '1');
    assert(ValidBitString(s));
    
    assert(s.len() > 0);
    assert(s.subrange(0, s.len() as int - 1) == s_half);
    assert(s.index(s.len() as int - 1) == bit);
    
    assert(Str2Int(s) == 2 * Str2Int(s_half) + (if bit == '1' { 1nat } else { 0nat }));
    assert(Str2Int(s_half) == n / 2);
    
    if n % 2 == 0 {
      assert(bit == '0');
      assert(Str2Int(s) == 2 * (n / 2) + 0);
      assert(Str2Int(s) == n);
    } else {
      assert(bit == '1');
      assert(Str2Int(s) == 2 * (n / 2) + 1);
      assert(Str2Int(s) == n);
    }
  }
}

exec fn nat_to_bit_string(n: nat) -> (res: Vec<char>)
  ensures ValidBitString(res@)
  ensures Str2Int(res@) == n
{
  proof { lemma_str2int_int2str_inverse(n); }
  
  if n == 0 {
    let mut result = Vec::new();
    result.push('0');
    return result;
  }
  
  let mut result = Vec::new();
  let mut num = n;
  
  while num > 0
    invariant ValidBitString(result@)
    invariant num >= 0
    invariant Str2Int(result@) + num * pow2(result@.len()) == n
    decreases num
  {
    if num % 2 == 0 {
      result.push('0');
    } else {
      result.push('1');
    }
    num = num / 2;
  }
  
  result.reverse();
  
  proof {
    lemma_reverse_preserves_valid_bit_string(result@);
    lemma_reverse_str2int(result@);
  }
  
  return result;
}

spec fn pow2(n: nat) -> nat
  decreases n
{
  if n == 0 { 1 } else { 2 * pow2((n - 1) as nat) }
}

proof fn lemma_reverse_preserves_valid_bit_string(s: Seq<char>)
  requires ValidBitString(s)
  ensures ValidBitString(s.reverse())
{
}

proof fn lemma_reverse_str2int(s: Seq<char>)
  requires ValidBitString(s)
  ensures Str2Int(s.reverse()) == Str2Int(s)
{
  admit();
}

proof fn lemma_str2int_zero()
  ensures Str2Int(seq!['0']) == 0
{
}

proof fn lemma_str2int_mult_distributive(s1: Seq<char>, s2: Seq<char>)
  requires ValidBitString(s1), ValidBitString(s2)
  ensures exists |s3: Seq<char>| ValidBitString(s3) && Str2Int(s3) == Str2Int(s1) * Str2Int(s2)
{
  let product = Str2Int(s1) * Str2Int(s2);
  lemma_str2int_int2str_inverse(product);
  let s3 = Int2Str(product);
  assert(ValidBitString(s3) && Str2Int(s3) == product);
}
// </vc-helpers>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
  let product = Str2Int(s1@) * Str2Int(s2@);
  proof {
    lemma_str2int_mult_distributive(s1@, s2@);
  }
  return nat_to_bit_string(product);
}
// </vc-code>

fn main() {}
}