// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn power_of_base(base: int, exp: int) -> int
  decreases exp
{
  if base >= 2 && exp >= 0 {
    if exp == 0 { 1 } else { base * power_of_base(base, exp - 1) }
  } else {
    0
  }
}

spec fn digits_to_int(digits: Seq<char>, base: int) -> int
  decreases digits.len()
{
  if base >= 2 && (forall|i: int| 0 <= i < digits.len() ==> '0' <= digits[i] <= '9' && (digits[i] as int) - ('0' as int) < base) {
    if digits.len() == 0 { 0 }
    else { (digits[0] as int) - ('0' as int) + base * digits_to_int(digits.subrange(1, digits.len() as int), base) }
  } else {
    0
  }
}

spec fn string_to_int_in_base(s: Seq<char>, base: int) -> int
  decreases s.len()
{
  if base >= 2 && s.len() > 0 && (forall|i: int| 0 <= i < s.len() ==> '0' <= s[i] <= '9' && (s[i] as int) - ('0' as int) < base) {
    if s.len() == 1 {
      (s[0] as int) - ('0' as int)
    } else {
      string_to_int_in_base(s.subrange(0, s.len() - 1), base) * base + ((s[s.len() - 1] as int) - ('0' as int))
    }
  } else {
    0
  }
}
// </vc-preamble>

// <vc-helpers>
spec fn reverse_sequence<T>(s: Seq<T>) -> Seq<T>
    decreases s.len()
{
    if s.len() == 0 {
        seq![]
    } else {
        reverse_sequence(s.subrange(1, s.len() as int)) + seq![s[0]]
    }
}
// </vc-helpers>

// <vc-spec>
fn change_base(x: i8, base: i8) -> (result: Vec<char>)
  requires 
    base >= 2 && base < 10,
    x >= 0,
  ensures 
    x as int == 0 ==> result@ == seq!['0'],
    x as int > 0 ==> result@.len() > 0 && result@[0] != '0',
    forall|i: int| 0 <= i < result@.len() ==> '0' <= result@[i] <= '9' && (result@[i] as int) - ('0' as int) < base as int,
    x as int > 0 ==> string_to_int_in_base(result@, base as int) == x as int,
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): fixed compilation error by manually reversing the vector instead of using the reverse method */
  if x == 0 {
      return vec!['0'];
  }

  let mut current = x;
  let mut digits = Vec::new();

  while current > 0
      invariant
          current >= 0,
          x as int == current as int * power_of_base(base as int, digits@.len() as int) + 
              string_to_int_in_base(reverse_sequence(digits@), base as int),
          digits.len() >= 0,
      decreases current
  {
      let remainder = current % base;
      let digit_char = (remainder as u8 + 48) as char;
      digits.push(digit_char);
      current = current / base;
  }

  // Manually reverse the vector
  let mut result = Vec::new();
  let mut i = digits.len() as int;
  while i > 0
      invariant 0 <= i <= digits.len() as int,
      invariant result.len() == (digits.len() as int - i) as usize,
      decreases i
  {
      i -= 1;
      result.push(digits[i]);
  }

  result
}
// </vc-code>


}

fn main() {}