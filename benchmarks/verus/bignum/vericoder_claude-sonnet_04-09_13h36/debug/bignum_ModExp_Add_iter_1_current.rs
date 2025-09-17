use vstd::prelude::*;

verus! {

spec fn Exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 { 1 } else { x * Exp_int(x, (y - 1) as nat) }
}

spec fn Str2Int(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  if s.len() == 0 { 0 } else { 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat }) }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==> (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
lemma lemma_str2int_empty()
  ensures Str2Int(Seq::<char>::empty()) == 0
{}

lemma lemma_str2int_append_bit(s: Seq<char>, bit: char)
  requires ValidBitString(s), bit == '0' || bit == '1'
  ensures ValidBitString(s.push(bit))
  ensures Str2Int(s.push(bit)) == 2 * Str2Int(s) + (if bit == '1' { 1nat } else { 0nat })
{
  let new_s = s.push(bit);
  assert(new_s.len() > 0);
  assert(new_s.subrange(0, new_s.len() as int - 1) =~= s);
  assert(new_s.index(new_s.len() as int - 1) == bit);
}

lemma lemma_str2int_distributive(s1: Seq<char>, s2: Seq<char>)
  requires ValidBitString(s1), ValidBitString(s2)
  ensures ValidBitString(s1 + s2)
  decreases s2.len()
{
  if s2.len() == 0 {
    assert(s1 + s2 =~= s1);
  } else {
    let s2_init = s2.subrange(0, s2.len() as int - 1);
    let s2_last = s2.index(s2.len() as int - 1);
    lemma_str2int_distributive(s1, s2_init);
    assert(s1 + s2 =~= (s1 + s2_init).push(s2_last));
  }
}

exec fn char_to_digit(c: char) -> (res: nat)
  requires c == '0' || c == '1'
  ensures res == 0 || res == 1
  ensures res == (if c == '1' { 1nat } else { 0nat })
{
  if c == '1' { 1 } else { 0 }
}

exec fn digit_to_char(d: nat) -> (res: char)
  requires d == 0 || d == 1
  ensures res == '0' || res == '1'
  ensures d == (if res == '1' { 1nat } else { 0nat })
{
  if d == 1 { '1' } else { '0' }
}

lemma lemma_valid_bit_string_reverse(s: Seq<char>)
  requires ValidBitString(s)
  ensures ValidBitString(s.reverse())
{
  assert forall |i: int| 0 <= i && i < s.reverse().len() ==> {
    let orig_i = s.len() as int - 1 - i;
    0 <= orig_i && orig_i < s.len() as int && 
    s.reverse().index(i) == s.index(orig_i) &&
    (s.index(orig_i) == '0' || s.index(orig_i) == '1')
  };
}

spec fn str2int_little_endian(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  if s.len() == 0 { 0 } else { 
    (if s.index(0) == '1' { 1nat } else { 0nat }) + 2 * str2int_little_endian(s.subrange(1, s.len() as int))
  }
}

lemma lemma_str2int_reverse_equiv(s: Seq<char>)
  requires ValidBitString(s)
  ensures Str2Int(s) == str2int_little_endian(s.reverse())
  decreases s.len()
{
  if s.len() == 0 {
    assert(s.reverse() =~= Seq::<char>::empty());
  } else {
    let s_init = s.subrange(0, s.len() as int - 1);
    let s_last = s.index(s.len() as int - 1);
    let s_rev = s.reverse();
    
    assert(s_rev.len() > 0);
    assert(s_rev.index(0) == s_last);
    assert(s_rev.subrange(1, s_rev.len() as int) =~= s_init.reverse());
    
    lemma_str2int_reverse_equiv(s_init);
  }
}
// </vc-helpers>

// <vc-spec>
exec fn Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
  let mut result = Vec::<char>::new();
  let mut carry = 0nat;
  let mut i1 = s1.len();
  let mut i2 = s2.len();
  
  while i1 > 0 || i2 > 0 || carry > 0
    invariant 
      i1 <= s1.len(),
      i2 <= s2.len(),
      carry <= 2,
      ValidBitString(result@),
      ValidBitString(s1@),
      ValidBitString(s2@)
  {
    let mut sum = carry;
    
    if i1 > 0 {
      i1 = i1 - 1;
      let digit = char_to_digit(s1[i1]);
      sum = sum + digit;
    }
    
    if i2 > 0 {
      i2 = i2 - 1;
      let digit = char_to_digit(s2[i2]);
      sum = sum + digit;
    }
    
    let result_digit = sum % 2;
    carry = sum / 2;
    
    let result_char = digit_to_char(result_digit);
    result.push(result_char);
  }
  
  result.reverse();
  
  proof {
    lemma_valid_bit_string_reverse(result@.reverse());
  }
  
  result
}
// </vc-code>

fn main() {}
}