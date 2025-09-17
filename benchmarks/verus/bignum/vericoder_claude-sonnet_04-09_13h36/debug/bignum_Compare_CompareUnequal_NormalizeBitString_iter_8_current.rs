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
  // All characters must be '0' or '1'.
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
proof fn lemma_str2int_subrange_leading_zeros(s: Seq<char>, start: int)
  requires
    ValidBitString(s),
    0 <= start < s.len(),
    forall |i: int| 0 <= i < start ==> s[i] == '0'
  ensures
    Str2Int(s) == Str2Int(s.subrange(start, s.len() as int))
  decreases start
{
  if start == 0 {
    assert(s.subrange(0, s.len() as int) =~= s);
  } else {
    lemma_str2int_leading_zero(s);
    lemma_str2int_subrange_leading_zeros(s.subrange(1, s.len() as int), start - 1);
    assert(s.subrange(start, s.len() as int) =~= s.subrange(1, s.len() as int).subrange(start - 1, s.len() as int - 1));
  }
}

proof fn lemma_str2int_leading_zero(s: Seq<char>)
  requires
    ValidBitString(s),
    s.len() > 0,
    s[0] == '0'
  ensures
    Str2Int(s) == Str2Int(s.subrange(1, s.len() as int))
  decreases s.len()
{
  if s.len() == 1 {
    assert(Str2Int(s) == 0);
    assert(s.subrange(1, 1) =~= Seq::<char>::empty());
    assert(Str2Int(s.subrange(1, 1)) == 0);
  } else {
    assert(Str2Int(s) == 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + 
           (if s[s.len() as int - 1] == '1' { 1nat } else { 0nat }));
    
    let s_prefix = s.subrange(0, s.len() as int - 1);
    let s_suffix = s.subrange(1, s.len() as int);
    
    assert(s_prefix[0] == '0');
    lemma_str2int_leading_zero(s_prefix);
    
    assert(Str2Int(s_prefix) == Str2Int(s_prefix.subrange(1, s_prefix.len() as int)));
    assert(s_prefix.subrange(1, s_prefix.len() as int) =~= s_suffix.subrange(0, s_suffix.len() as int - 1));
    
    assert(Str2Int(s) == 2 * Str2Int(s_suffix.subrange(0, s_suffix.len() as int - 1)) +
           (if s_suffix[s_suffix.len() as int - 1] == '1' { 1nat } else { 0nat }));
    assert(Str2Int(s) == Str2Int(s_suffix));
  }
}

proof fn lemma_valid_bitstring_subrange(s: Seq<char>, start: int, end: int)
  requires
    ValidBitString(s),
    0 <= start <= end <= s.len()
  ensures
    ValidBitString(s.subrange(start, end))
{
}

proof fn lemma_str2int_all_zeros(n: int)
  requires n >= 1
  ensures Str2Int(Seq::<char>::new(n as nat, |i: int| '0').take(n)) == 0
  decreases n
{
  let zeros = Seq::<char>::new(n as nat, |i: int| '0').take(n);
  if n == 1 {
    assert(Str2Int(zeros) == 0);
  } else {
    lemma_str2int_all_zeros(n - 1);
  }
}
// </vc-helpers>

// <vc-spec>
exec fn NormalizeBitString(s: &[char]) -> (t: Vec<char>)
  ensures ValidBitString(t@),
   t@.len() > 0,
   t@.len() > 1 ==> t@[0] != '0',
   ValidBitString(s@) ==> Str2Int(s@) == Str2Int(t@)
// </vc-spec>
// <vc-code>
{
  let mut result = Vec::new();
  
  // Copy all characters to result
  for i in 0..s.len()
    invariant
      result.len() == i,
      ValidBitString(result@),
      forall |j: int| 0 <= j < i ==> result@[j] == s@[j]
  {
    result.push(s[i]);
  }
  
  // After the loop, result is a copy of s
  assert(result@ == s@);
  
  // Find first non-zero character
  let mut first_one = 0;
  while first_one < result.len() && result[first_one] == '0'
    invariant
      first_one <= result.len(),
      ValidBitString(result@),
      result@ == s@,
      forall |j: int| 0 <= j < first_one ==> result@[j] == '0'
    decreases result.len() - first_one
  {
    first_one += 1;
  }
  
  if first_one == result.len() {
    // All zeros case
    result.truncate(1);
    proof {
      if ValidBitString(s@) {
        lemma_str2int_all_zeros(s@.len() as int);
      }
    }
  } else {
    // Remove leading zeros by creating a new vector
    let mut new_result = Vec::new();
    
    for i in first_one..result.len()
      invariant
        new_result.len() == i - first_one,
        ValidBitString(new_result@),
        forall |j: int| 0 <= j < new_result@.len() ==> 
          new_result@[j] == result@[first_one as int + j]
    {
      new_result.push(result[i]);
    }
    
    proof {
      let old_result = result@;
      assert(new_result@ =~= old_result.subrange(first_one as int, old_result.len() as int));
      lemma_valid_bitstring_subrange(old_result, first_one as int, old_result.len() as int);
      if ValidBitString(s@) {
        lemma_str2int_subrange_leading_zeros(old_result, first_one as int);
      }
    }
    
    result = new_result;
  }
  
  result
}
// </vc-code>

fn main() {}
}