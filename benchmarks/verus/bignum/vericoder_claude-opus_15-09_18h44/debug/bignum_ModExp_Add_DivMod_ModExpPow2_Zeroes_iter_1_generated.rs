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
    Int2Str(n / 2).push(if n % 2 == 0 { '0' } else { '1' })
  }
}

proof fn lemma_str2int_int2str(n: nat)
  ensures ValidBitString(Int2Str(n)),
          Str2Int(Int2Str(n)) == n
  decreases n
{
  if n > 1 {
    lemma_str2int_int2str(n / 2);
  }
}

proof fn lemma_int2str_str2int(s: Seq<char>)
  requires ValidBitString(s),
           s.len() > 0
  ensures Int2Str(Str2Int(s)) == s
  decreases s.len()
{
  if s.len() > 1 {
    lemma_int2str_str2int(s.subrange(0, s.len() as int - 1));
  }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_DivMod_ModExpPow2_Zeroes(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
  let a_val = Str2Int(a@);
  let b_val = Str2Int(b@);
  let sum = a_val + b_val;
  
  proof {
    lemma_str2int_int2str(sum);
  }
  
  let mut result = Vec::<char>::new();
  let sum_str = Int2Str(sum);
  
  let mut i: usize = 0;
  while i < sum_str.len()
    invariant
      i <= sum_str.len(),
      result@.len() == i as int,
      forall |j: int| 0 <= j && j < i as int ==> result@[j] == sum_str[j],
      ValidBitString(result@)
  {
    result.push(sum_str[i as int]);
    i = i + 1;
  }
  
  result
}
// </vc-code>

fn main() {}
}

