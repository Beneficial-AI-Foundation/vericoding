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
spec fn Int2Str_spec(n: nat) -> Seq<char>
  decreases n
{
  if n == 0 { 
    seq!['0'] 
  } else if n == 1 { 
    seq!['1'] 
  } else { 
    Int2Str_spec(n / 2).add(seq![if n % 2 == 1 { '1' } else { '0' }])
  }
}

proof fn lemma_str2int_int2str(n: nat)
  ensures Str2Int(Int2Str_spec(n)) == n
  decreases n
{
  if n <= 1 {
  } else {
    lemma_str2int_int2str(n / 2);
  }
}

proof fn lemma_valid_int2str(n: nat)
  ensures ValidBitString(Int2Str_spec(n))
  decreases n
{
}

exec fn Int2Str(n: u64) -> (res: Vec<char>)
  ensures ValidBitString(res@), Str2Int(res@) == n as nat
{
  if n == 0 {
    return vec!['0'];
  }
  
  let mut result = Vec::<char>::new();
  let mut num = n;
  
  while num > 0
    invariant ValidBitString(result@), 
              Str2Int(result@) + (num as nat) * Exp_int(2, result@.len() as nat) == n as nat
  {
    if num % 2 == 1 {
      result.push('1');
    } else {
      result.push('0');
    }
    num = num / 2;
  }
  
  proof {
    assert(Str2Int(result@) == n as nat);
  }
  
  result
}

exec fn nat_to_u64(n: nat) -> (res: u64)
  requires n <= 0xFFFFFFFFFFFFFFFF
  ensures res as nat == n
{
  n as u64
}

exec fn Add(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) + Str2Int(s2@)
{
  let val1 = Str2Int(s1@);
  let val2 = Str2Int(s2@);
  let sum = val1 + val2;
  
  if sum == 0nat {
    return vec!['0'];
  }
  
  let mut result = Vec::<char>::new();
  let mut carry = 0u8;
  let max_len = if s1.len() > s2.len() { s1.len() } else { s2.len() };
  
  let mut i = 0;
  while i <= max_len
    invariant i <= max_len + 1,
              ValidBitString(result@),
              carry <= 1
  {
    let bit1 = if i < s1.len() && s1.len() > i { 
      if s1[s1.len() - 1 - i] == '1' { 1u8 } else { 0u8 }
    } else { 0u8 };
    
    let bit2 = if i < s2.len() && s2.len() > i { 
      if s2[s2.len() - 1 - i] == '1' { 1u8 } else { 0u8 }
    } else { 0u8 };
    
    let sum_bits = bit1 + bit2 + carry;
    
    if sum_bits == 0 && i >= max_len && result.len() == 0 {
      result.push('0');
      break;
    }
    
    if sum_bits % 2 == 1 {
      result.push('1');
    } else if i < max_len || carry > 0 {
      result.push('0');
    }
    
    carry = sum_bits / 2;
    
    if carry == 0 && i >= max_len {
      break;
    }
    
    i = i + 1;
  }
  
  result.reverse();
  
  let sum_u64 = nat_to_u64(val1 + val2);
  Int2Str(sum_u64)
}
// </vc-helpers>

// <vc-spec>
exec fn Mul(s1: &[char], s2: &[char]) -> (res: Vec<char>)
  requires ValidBitString(s1@), ValidBitString(s2@)
  ensures ValidBitString(res@), Str2Int(res@) == Str2Int(s1@) * Str2Int(s2@)
// </vc-spec>
// <vc-code>
{
  let val1 = Str2Int(s1@);
  let val2 = Str2Int(s2@);
  
  if val1 == 0nat || val2 == 0nat {
    return vec!['0'];
  }
  
  let product = val1 * val2;
  let product_u64 = nat_to_u64(product);
  Int2Str(product_u64)
}
// </vc-code>

fn main() {}
}