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
  ensures ValidBitString(res@),
  ensures Str2Int(res@) == n
{
  proof {
    lemma_str2int_int2str_inverse(n);
  }
  
  let product_str = Int2Str(n);
  let mut result = Vec::new();
  
  for i in 0..product_str.len()
    invariant 
      0 <= i <= product_str.len(),
      ValidBitString(result@),
      result@.len() == i,
      forall |j: int| 0 <= j < i ==> result@[j] == product_str[j]
  {
    result.push(product_str[i as int]);
  }
  
  proof {
    assert(result@.len() == product_str.len());
    assert(forall |j: int| 0 <= j < result@.len() ==> result@[j] == product_str[j]);
    assert(result@ == product_str);
    assert(ValidBitString(result@));
    assert(Str2Int(result@) == n);
  }
  
  result
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
  nat_to_bit_string(product)
}
// </vc-code>

fn main() {}
}