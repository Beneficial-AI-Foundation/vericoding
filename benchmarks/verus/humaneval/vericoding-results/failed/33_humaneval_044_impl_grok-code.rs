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
spec fn reversed_digits_value(digits: Seq<char>, base: int) -> int
  decreases digits.len()
{
  if base >= 2 && (forall|i: int| 0 <= i < digits.len() ==> '0' <= digits[i] <= '9' && ((digits[i] as int) - ('0' as int)) < base) {
    if digits.len() == 0 { 0 }
    else { ((digits[digits.len() - 1] as int) - ('0' as int)) + base * reversed_digits_value(digits.subrange(0, digits.len() - 1), base) }
  } else { 0 }
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
/* code modified by LLM (iteration 5): fixed types to use i32 for executable code instead of int */
{
  if x == 0 {
    let mut result = Vec::new();
    result.push('0');
    return result;
  } else {
    let mut result = Vec::new();
    let mut num = x as i32;
    let base_int = base as i32;
    let mut power = 1i32;
    while power * base_int <= num {
      power = power * base_int;
    }
    while power > 0 
      invariant
        power >= 1,
        power <= x as int + 1,
        num >= 0,
        num < power,
        forall|i: int| 0 <= i < result@.len() ==> '0' <= result@[i] <= '9' && (result@[i] as int) - ('0' as int) < base_int as int,
      decreases power as int
    {
      let digit = num / power;
      let ch = ((digit as u8) + ('0' as u8)) as char;
      result.push(ch);
      num = num % power;
      power = power / base_int;
    }
    return result;
  }
}
// </vc-code>


}

fn main() {}