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
/* helper modified by LLM (iteration 5): Fix compilation error in subrange arguments to use int for both parameters */

spec fn is_digit(c: char, base: int) -> bool
  recommends 2 <= base < 10
{
  '0' <= c <= '9' && (c as int) - ('0' as int) < base
}

proof fn power_of_base_positive(base: int, exp: int)
  requires
    base >= 2,
    exp >= 0,
  ensures
    power_of_base(base, exp) > 0,
  decreases exp
{
  if exp > 0 {
    power_of_base_positive(base, exp - 1);
  }
}

proof fn digits_to_int_properties(digits: Seq<char>, base: int)
  requires
    base >= 2,
    forall|i: int| 0 <= i < digits.len() ==> is_digit(digits[i], base),
  ensures
    digits_to_int(digits, base) >= 0,
    digits.len() > 0 ==> (digits_to_int(digits, base) as int >= (digits[0] as int) - ('0' as int)),
  decreases digits.len()
{
  if digits.len() > 0 {
    digits_to_int_properties(digits.subrange(1, digits.len() as int), base);
    power_of_base_positive(base, digits.len() as int - 1);
  }
}

proof fn string_to_int_equivalence(digits: Seq<char>, base: int)
  requires
    base >= 2,
    forall|i: int| 0 <= i < digits.len() ==> is_digit(digits[i], base),
  ensures
    digits_to_int(digits, base) == string_to_int_in_base(digits, base),
  decreases digits.len()
{
  if digits.len() > 1 {
    let first = (digits[0] as int) - ('0' as int);
    let rest = digits.subrange(1, digits.len() as int);
    string_to_int_equivalence(rest, base);
  }
}

proof fn reverse_invariant_preserved(original: Seq<char>, reversed: Seq<char>, base: int, x: int)
  requires
    base >= 2,
    forall|i: int| 0 <= i < original.len() ==> is_digit(original[i], base),
    string_to_int_in_base(original, base) == x,
    reversed == original.reverse(),
  ensures
    string_to_int_in_base(reversed, base) == x,
    reversed.len() > 0 ==> reversed[0] != '0',
  decreases original.len()
{
  if original.len() > 1 {
    let first_char = original[0];
    let last_char = original[original.len() - 1];
    let middle = original.subrange(1, original.len() - 1);
    reverse_invariant_preserved(middle, reversed.subrange(1, reversed.len() - 1), base, (x - (last_char as int - '0' as int)) / base);
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
/* code modified by LLM (iteration 5): Fix compilation error by casting len() to int in subrange arguments */
{
  if x == 0 {
    return vec!['0'];
  }
  
  let mut result_vec = Vec::new();
  let mut remaining = x;
  
  while remaining > 0
      invariant
          remaining >= 0,
          result_vec@.len() > 0 ==> result_vec@[0] != '0',
          forall|i: int| 0 <= i < result_vec@.len() ==> is_digit(result_vec@[i], base as int),
          string_to_int_in_base(result_vec@, base as int) + (remaining as int) * power_of_base(base as int, result_vec@.len() as int) == x as int,
      decreases remaining
  {
    let digit_value = remaining % base;
    remaining = remaining / base;
    
    let digit_char = (digit_value as u8 + b'0') as char;
    result_vec.push(digit_char);
    
    proof {
      power_of_base_positive(base as int, result_vec@.len() as int - 1);
      string_to_int_equivalence(result_vec@, base as int);
    }
  }
  
  proof {
    digits_to_int_properties(result_vec@, base as int);
  }
  
  let mut reversed_vec = Vec::new();
  let mut i = (result_vec.len() as isize) - 1;
  while i >= 0
      invariant
          i >= -1,
          reversed_vec@ == result_vec@.subrange((i + 1) as int, result_vec@.len() as int).reverse(),
          forall|j: int| 0 <= j < reversed_vec@.len() ==> is_digit(reversed_vec@[j], base as int)
  {
    reversed_vec.push(result_vec[i as usize]);
    i = i - 1;
  }
  
  proof {
    reverse_invariant_preserved(result_vec@, reversed_vec@, base as int, x as int);
  }
  
  reversed_vec
}
// </vc-code>


}

fn main() {}