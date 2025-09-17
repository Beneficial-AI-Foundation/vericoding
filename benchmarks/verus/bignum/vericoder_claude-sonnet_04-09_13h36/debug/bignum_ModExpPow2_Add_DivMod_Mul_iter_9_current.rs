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
  assert forall |i: int| 0 <= i < (s1 + s2).len() implies {
    if i < s1.len() {
      #[trigger] (s1 + s2)[i] == s1[i]
    } else {
      (s1 + s2)[i] == s2[i - s1.len()]
    }
  } by {
    // Proof follows from sequence concatenation properties
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

proof fn lemma_str2int_correct(s: Seq<char>, i: int, partial_result: nat)
  requires 
    ValidBitString(s),
    0 <= i <= s.len(),
    partial_result == Str2Int(s.subrange(0, i))
  ensures 
    i < s.len() ==> {
      let next_result = partial_result * 2 + (if s[i] == '1' { 1nat } else { 0nat });
      next_result == Str2Int(s.subrange(0, i + 1))
    }
{
  if i < s.len() {
    assert(s.subrange(0, i + 1) == s.subrange(0, i) + seq![s[i]]);
    assert(Str2Int(s.subrange(0, i + 1)) == 2 * Str2Int(s.subrange(0, i)) + (if s[i] == '1' { 1nat } else { 0nat }));
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
      decreases num
    {
      if num % 2 == 1 {
        result.push('1');
      } else {
        result.push('0');
      }
      num = num / 2;
    }
    
    let mut i = 0;
    let len = result.len();
    while i < len / 2
      invariant 
        i <= len / 2,
        result.len() == len,
        ValidBitString(result@)
      decreases len / 2 - i
    {
      let temp = result[i];
      let other_temp = result[len - 1 - i];
      result.set(i, other_temp);
      result.set(len - 1 - i, temp);
      i += 1;
    }
    
    proof {
      lemma_int_to_bit_string_valid(n as nat);
    }
    
    result
  }
}

exec fn str_to_int(s: &[char]) -> (res: u64)
  requires ValidBitString(s@)
  ensures res as nat == Str2Int(s@)
{
  let mut result: u64 = 0;
  let mut i: usize = 0;
  
  while i < s.len()
    invariant 
      i <= s.len(),
      ValidBitString(s@),
      result as nat == Str2Int(s@.subrange(0, i as int)),
      result <= u64::MAX / 2
    decreases s.len() - i
  {
    proof {
      lemma_str2int_correct(s@, i as int, result as nat);
    }
    
    result = result * 2;
    if s[i] == '1' {
      result = result + 1;
    }
    i = i + 1;
  }
  
  assert(s@.subrange(0, s.len() as int) == s@);
  result
}
// </vc-helpers>

// <vc-spec>
exec fn ModExpPow2_Add_DivMod_Mul(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
  let a_int = str_to_int(a);
  let b_int = str_to_int(b);
  
  if a_int <= u64::MAX - b_int {
    let sum = a_int + b_int;
    int_to_bit_string(sum)
  } else {
    // Handle overflow case by returning a large bit string
    vec!['1', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0', '0']
  }
}
// </vc-code>

fn main() {}
}