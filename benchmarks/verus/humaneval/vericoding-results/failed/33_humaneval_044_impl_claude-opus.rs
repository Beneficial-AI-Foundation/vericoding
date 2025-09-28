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
proof fn lemma_string_to_int_push(s: Seq<char>, base: int, digit: char)
    requires
        base >= 2,
        s.len() >= 0,
        '0' <= digit <= '9',
        (digit as int) - ('0' as int) < base,
        forall|i: int| 0 <= i < s.len() ==> '0' <= s[i] <= '9' && (s[i] as int) - ('0' as int) < base,
    ensures
        string_to_int_in_base(s.push(digit), base) == string_to_int_in_base(s, base) * base + ((digit as int) - ('0' as int)),
    decreases s.len(),
{
    if s.len() == 0 {
        assert(s.push(digit).len() == 1);
        assert(string_to_int_in_base(s.push(digit), base) == (digit as int) - ('0' as int));
        assert(string_to_int_in_base(s, base) == 0);
    } else {
        let s_push = s.push(digit);
        assert(s_push.len() == s.len() + 1);
        assert(s_push.subrange(0, s_push.len() - 1) =~= s);
        assert(s_push[s_push.len() - 1] == digit);
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
    if x == 0 {
        let mut result = Vec::new();
        result.push('0');
        return result;
    }
    
    let mut result = Vec::new();
    let mut num = x;
    
    while num > 0
        invariant
            base >= 2 && base < 10,
            num >= 0,
            forall|i: int| 0 <= i < result@.len() ==> '0' <= result@[i] <= '9' && (result@[i] as int) - ('0' as int) < base as int,
            result@.len() == 0 || result@[0] != '0',
            x as int == string_to_int_in_base(result@, base as int) * power_of_base(base as int, (x as int).log(base as int) + 1 - result@.len() as int) + num as int,
        decreases num,
    {
        let digit = (num % base) as char + '0' as char;
        proof {
            lemma_string_to_int_push(result@, base as int, digit);
        }
        result.push(digit);
        num = num / base;
    }
    
    result
}
// </vc-code>


}

fn main() {}