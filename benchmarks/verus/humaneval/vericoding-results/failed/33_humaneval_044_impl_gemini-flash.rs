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
/* code modified by LLM (iteration 5): Replaced usage of Vec::reverse() with explicit loop to reverse the digits. */
{
    if x == 0 {
        return vec!['0'];
    }

    let mut temp_vec: Vec<char> = Vec::new();
    let mut current_x: i8 = x;

    while current_x > 0
        invariant
            current_x >= 0,
            current_x < x + 1,
            base >= 2,
            // All digits collected so far are valid for the base
            forall|i: int| 0 <= i < temp_vec@.len() ==> '0' <= temp_vec@[i] <= '9' && (temp_vec@[i] as int) - ('0' as int) < base as int,
            // The parts of the number that have been processed and the current_x make up the original x
            // x as int == current_x as int * power_of_base(base as int, temp_vec@.len() as int) + string_to_int_in_base(temp_vec@.reverse(), base as int),
        decreases current_x
    {
        let remainder: i8 = current_x % base;
        let digit_char: char = (('0' as u8) + remainder as u8) as char;

        temp_vec.push(digit_char);
        current_x = current_x / base;
    }

    let mut result_vec: Vec<char> = Vec::new();
    let mut i: usize = temp_vec.len();
    while i > 0
        invariant
            i <= temp_vec.len(),
            result_vec@.len() == (temp_vec.len() as int) - (i as int),
            forall|j: int| 0 <= j < result_vec@.len() ==> '0' <= result_vec@[j] <= '9' && (result_vec@[j] as int) - ('0' as int) < base as int,
            forall|j: int| 0 <= j < result_vec@.len() ==> result_vec@[j] == temp_vec@[temp_vec.len() - 1 - (j as usize)],
        decreases i
    {
        i = i - 1;
        result_vec.push(temp_vec[i]);
    }
    
    result_vec
}
// </vc-code>


}

fn main() {}