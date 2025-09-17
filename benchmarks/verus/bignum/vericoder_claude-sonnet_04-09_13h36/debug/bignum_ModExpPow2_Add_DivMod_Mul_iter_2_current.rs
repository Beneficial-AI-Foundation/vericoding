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
spec fn int_to_bit_string_spec(n: nat) -> Seq<char>
  decreases n
{
  if n == 0 {
    seq!['0']
  } else {
    int_to_bit_string_spec(n / 2) + seq![if n % 2 == 1 { '1' } else { '0' }]
  }
}

proof fn lemma_valid_bit_string_concat(s1: Seq<char>, s2: Seq<char>)
  requires ValidBitString(s1), ValidBitString(s2)
  ensures ValidBitString(s1 + s2)
{
  assert forall |i: int| 0 <= i < (s1 + s2).len() ==> {
    if i < s1.len() {
      (s1 + s2)[i] == s1[i]
    } else {
      (s1 + s2)[i] == s2[i - s1.len()]
    }
  };
}

proof fn lemma_int_to_bit_string_valid(n: nat)
  ensures ValidBitString(int_to_bit_string_spec(n))
  decreases n
{
  if n == 0 {
    assert(ValidBitString(seq!['0']));
  } else {
    lemma_int_to_bit_string_valid(n / 2);
    lemma_valid_bit_string_concat(
      int_to_bit_string_spec(n / 2), 
      seq![if n % 2 == 1 { '1' } else { '0' }]
    );
  }
}

exec fn int_to_bit_string(n: u64) -> (res: Vec<char>)
  ensures ValidBitString(res@)
{
  if n == 0 {
    vec!['0']
  } else {
    let mut result = Vec::new();
    let mut num = n;
    
    while num > 0
      invariant ValidBitString(result@)
    {
      if num % 2 == 1 {
        result.push('1');
      } else {
        result.push('0');
      }
      num = num / 2;
    }
    
    result.reverse();
    
    proof {
      lemma_int_to_bit_string_valid(n as nat);
    }
    
    result
  }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExpPow2_Add_DivMod_Mul(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
  let a_int = Str2Int(a@);
  let b_int = Str2Int(b@);
  let sum = a_int + b_int;
  
  if sum == 0 {
    vec!['0']
  } else {
    int_to_bit_string(sum as u64)
  }
}
// </vc-code>

fn main() {}
}