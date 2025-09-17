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
proof fn Str2Int_empty() 
  ensures Str2Int(Seq::<char>::empty()) == 0
{
}

proof fn Str2Int_append(s: Seq<char>, c: char) 
  requires ValidBitString(s), c == '0' || c == '1'
  ensures ValidBitString(s.push(c)),
          Str2Int(s.push(c)) == 2 * Str2Int(s) + (if c == '1' { 1nat } else { 0nat })
{
}

proof fn Exp_int_properties(x: nat, y: nat) 
  ensures Exp_int(x, 0) == 1,
          y > 0 ==> Exp_int(x, y) == x * Exp_int(x, (y - 1) as nat)
{
}

proof fn ValidBitString_append(s: Seq<char>, c: char) 
  requires ValidBitString(s), c == '0' || c == '1'
  ensures ValidBitString(s.push(c))
{
}

proof fn ValidBitString_empty() 
  ensures ValidBitString(Seq::<char>::empty())
{
}

proof fn Str2Int_single_bit(c: char) 
  requires c == '0' || c == '1'
  ensures Str2Int(seq![c]) == (if c == '1' { 1nat } else { 0nat })
{
}

proof fn valid_bit_char(c: char)
  requires c == '0' || c == '1'
  ensures ValidBitString(seq![c])
{
}

proof fn str2int_cons(s: Seq<char>, c: char)
  requires ValidBitString(s), c == '0' || c == '1'
  ensures Str2Int(seq![c] + s) == (if c == '1' { 1nat } else { 0nat }) * Exp_int(2, s.len()) + Str2Int(s)
{
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
  let mut carry = false;
  let mut i1 = s1.len();
  let mut i2 = s2.len();
  
  while i1 > 0 || i2 > 0 || carry
    invariant
      ValidBitString(result@),
      i1 <= s1.len(),
      i2 <= s2.len(),
      ValidBitString(s1@),
      ValidBitString(s2@)
  {
    let bit1 = if i1 > 0 {
      i1 = i1 - 1;
      s1[i1]
    } else {
      '0'
    };
    
    let bit2 = if i2 > 0 {
      i2 = i2 - 1;
      s2[i2]
    } else {
      '0'
    };
    
    assert(bit1 == '0' || bit1 == '1');
    assert(bit2 == '0' || bit2 == '1');
    
    let bit1_val = if bit1 == '1' { 1 } else { 0 };
    let bit2_val = if bit2 == '1' { 1 } else { 0 };
    let carry_val = if carry { 1 } else { 0 };
    let sum = bit1_val + bit2_val + carry_val;
    
    let result_bit = if sum % 2 == 1 { '1' } else { '0' };
    carry = sum >= 2;
    
    assert(result_bit == '0' || result_bit == '1');
    result.push(result_bit);
    
    proof {
      assert(ValidBitString(result@));
    }
  }
  
  let mut final_result = Vec::<char>::new();
  let mut k = result.len();
  while k > 0
    invariant
      ValidBitString(final_result@),
      k <= result.len(),
      ValidBitString(result@)
  {
    k = k - 1;
    final_result.push(result[k]);
    proof {
      assert(result[k] == '0' || result[k] == '1');
      assert(ValidBitString(final_result@));
    }
  }
  
  if final_result.len() == 0 {
    final_result.push('0');
  }
  
  proof {
    assert(ValidBitString(final_result@));
  }
  
  final_result
}
// </vc-code>

fn main() {}
}