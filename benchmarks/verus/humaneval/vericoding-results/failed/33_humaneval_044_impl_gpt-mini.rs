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
/* helper modified by LLM (iteration 5): rev_digits_to_int to interpret little-endian digit sequence */
spec fn rev_digits_to_int(digits: Seq<char>, base: int) -> int
  decreases digits.len()
{
  if base >= 2 && (forall|i: int| 0 <= i < digits.len() ==> '0' <= digits[i] <= '9' && (digits[i] as int) - ('0' as int) < base) {
    if digits.len() == 0 { 0 } else { (digits[0] as int) - ('0' as int) + base * rev_digits_to_int(digits.subrange(1, digits.len() as int), base) }
  } else {
    0
  }
}

/* helper modified by LLM (iteration 5): lemma for pushing a digit onto LSB-first sequence */
lemma fn rev_digits_push(old: Seq<char>, d: char, b: int)
  requires
    b >= 2,
    forall|i: int| 0 <= i < old.len() ==> '0' <= old[i] <= '9' && (old[i] as int) - ('0' as int) < b,
    '0' <= d && d <= '9' && (d as int) - ('0' as int) < b,
  ensures
    rev_digits_to_int(old + seq![d], b) == rev_digits_to_int(old, b) + ((d as int) - ('0' as int)) * power_of_base(b, old.len()),
  decreases old.len()
{
  if old.len() == 0 {
    // seq![d] case: rev_digits_to_int(seq![d]) = (d-'0')
    assert(rev_digits_to_int(seq![d], b) == ((d as int) - ('0' as int)));
    assert(power_of_base(b, 0) == 1);
    assert(rev_digits_to_int(seq![d], b) == rev_digits_to_int(Seq::empty(), b) + ((d as int) - ('0' as int)) * power_of_base(b, 0));
  } else {
    let rest = old.subrange(1, old.len());
    rev_digits_push(rest, d, b);
    // unfold definitions
    assert(rev_digits_to_int(old + seq![d], b) == (old[0] as int) - ('0' as int) + b * rev_digits_to_int(rest + seq![d], b));
    assert(rev_digits_to_int(old, b) == (old[0] as int) - ('0' as int) + b * rev_digits_to_int(rest, b));
    assert(rev_digits_to_int(rest + seq![d], b) == rev_digits_to_int(rest, b) + ((d as int) - ('0' as int)) * power_of_base(b, rest.len()));
    assert(power_of_base(b, old.len()) == b * power_of_base(b, rest.len()));
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
  /* code modified by LLM (iteration 5): implement base conversion with loop invariants and decreases clauses */
  let mut n: i32 = x as i32;
  let b: i32 = base as i32;
  let initial_x: int = x as int;
  let bb: int = base as int;
  let mut rev: Vec<char> = Vec::new();

  if n == 0 {
    rev.push('0');
  } else {
    while n > 0
        invariant
            n >= 0,
            initial_x == rev_digits_to_int(rev@, bb) + (n as int) * power_of_base(bb, rev@.len()),
            forall|i: int| 0 <= i < rev@.len() ==> '0' <= rev@[i] <= '9' && (rev@[i] as int) - ('0' as int) < bb,
        decreases n
    {
      let digit = (n % b) as i32;
      let c = (('0' as u8) + (digit as u8)) as char;
      rev.push(c);
      n = n / b;
      proof {
        // maintain invariant: relate push of last digit to rev_digits_to_int
        rev_digits_push(rev@.subrange(0, rev@.len() - 1), rev@[rev@.len() - 1], bb);
        assert(initial_x == rev_digits_to_int(rev@, bb) + (n as int) * power_of_base(bb, rev@.len()));
      }
    }
  }

  let mut res: Vec<char> = Vec::new();
  let orig_rev: Seq<char> = rev@;

  while rev.len() > 0
      invariant
          orig_rev == rev@ + res@,
          forall|i: int| 0 <= i < res@.len() ==> '0' <= res@[i] <= '9' && (res@[i] as int) - ('0' as int) < bb,
      decreases rev.len()
  {
    match rev.pop() {
      Some(c) => {
        res.push(c);
        proof {
          assert(orig_rev == rev@ + res@);
        }
      }
      None => (),
    }
  }

  res
}

// </vc-code>


}

fn main() {}