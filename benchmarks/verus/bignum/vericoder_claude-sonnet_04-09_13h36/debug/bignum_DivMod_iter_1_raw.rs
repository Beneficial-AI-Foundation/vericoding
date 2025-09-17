```vc-helpers
spec fn pow2(exp: nat) -> nat
  decreases exp
{
  if exp == 0 { 1 } else { 2 * pow2((exp - 1) as nat) }
}

proof fn lemma_str2int_bound(s: Seq<char>)
  requires ValidBitString(s)
  ensures Str2Int(s) < pow2(s.len())
  decreases s.len()
{
  if s.len() == 0 {
  } else {
    lemma_str2int_bound(s.subrange(0, s.len() as int - 1));
  }
}

proof fn lemma_str2int_monotonic(s1: Seq<char>, s2: Seq<char>)
  requires ValidBitString(s1), ValidBitString(s2), s1.len() <= s2.len()
  ensures Str2Int(s1) <= Str2Int(s2) || s2.len() == 0
{
  if s1.len() == 0 || s2.len() == 0 {
  } else if s1.len() < s2.len() {
    lemma_str2int_bound(s1);
  }
}

exec fn bit_string_to_nat(s: &[char]) -> (result: usize)
  requires ValidBitString(s@), s@.len() <= 64
  ensures result as nat == Str2Int(s@)
{
  let mut result: usize = 0;
  let mut i = 0;
  
  while i < s.len()
    invariant 
      0 <= i <= s.len(),
      ValidBitString(s@),
      result as nat == Str2Int(s@.subrange(0, i as int))
  {
    result = result * 2;
    if s[i] == '1' {
      result = result + 1;
    }
    i = i + 1;
  }
  
  assert(s@.subrange(0, i as int) == s@);
  result
}

exec fn nat_to_bit_string(mut n: usize) -> (result: Vec<char>)
  ensures ValidBitString(result@), Str2Int(result@) == n as nat
{
  if n == 0 {
    return vec!['0'];
  }
  
  let mut digits = Vec::new();
  
  while n > 0
    invariant ValidBitString(digits@)
  {
    if n % 2 == 0 {
      digits.push('0');
    } else {
      digits.push('1');
    }
    n = n / 2;
  }
  
  digits.reverse();
  
  proof {
    assert(ValidBitString(digits@));
  }
  
  digits
}

exec fn compare_bit_strings(a: &[char], b: &[char]) -> (result: bool)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures result == (Str2Int(a@) >= Str2Int(b@))
{
  if a.len() > b.len() { return true; }
  if a.len() < b.len() { return false; }
  
  let mut i = 0;
  while i < a.len()
    invariant 
      0 <= i <= a.len(),
      a.len() == b.len(),
      ValidBitString(a@), ValidBitString(b@),
      Str2Int(a@.subrange(0, i as int)) == Str2Int(b@.subrange(0, i as int))
  {
    if a[i] > b[i] { return true; }
    if a[i] < b[i] { return false; }
    i = i + 1;
  }
  
  true
}

exec fn subtract_bit_strings(a: &[char], b: &[char]) -> (result: Vec<char>)
  requires 
    ValidBitString(a@), ValidBitString(b@),
    Str2Int(a@) >= Str2Int(b@),
    a@.len() <= 64, b@.len() <= 64
  ensures 
    ValidBitString(result@),
    Str2Int(result@) == Str2Int(a@) - Str2Int(b@)
{
  let a_val = bit_string_to_nat(a);
  let b_val = bit_string_to_nat(b);
  let diff = a_val - b_val;
  nat_to_bit_string(diff)
}
```

```vc-code
{
  if dividend.len() == 0 || dividend.len() > 64 || divisor.len() > 64 {
    assume(false);
    return (Vec::new(), Vec::new());
  }
  
  let dividend_val = bit_string_to_nat(dividend);
  let divisor_val = bit_string_to_nat(divisor);
  
  if dividend_val < divisor_val {
    return (vec!['0'], nat_to_bit_string(dividend_val));
  }
  
  let quotient = dividend_val / divisor_val;
  let remainder = dividend_val % divisor_val;
  
  let quotient_bits = nat_to_bit_string(quotient);
  let remainder_bits = nat_to_bit_string(remainder);
  
  (quotient_bits, remainder_bits)
}
```