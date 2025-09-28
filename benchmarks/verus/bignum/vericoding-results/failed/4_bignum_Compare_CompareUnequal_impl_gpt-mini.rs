// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn str2int(s: Seq<char>) -> nat
  recommends valid_bit_string(s)
  decreases s.len()
{
  if s.len() == 0 {
    0nat
  } else {
    2nat * str2int(s.subrange(0, s.len() - 1)) + 
    (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
  }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

fn compare_unequal(s1: Seq<char>, s2: Seq<char>) -> (res: i32)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2),
    s1.len() > 0,
    s1.len() > 1 ==> s1[0] != '0',
    s2.len() > 0,
    s2.len() > 1 ==> s2[0] != '0',
    s1.len() > s2.len()
  ensures 
    str2int(s1) < str2int(s2) ==> res == -1,
    str2int(s1) == str2int(s2) ==> res == 0,
    str2int(s1) > str2int(s2) ==> res == 1
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 9): strip leading zeros and correctness proofs (fixed subrange index types) */

spec fn strip_leading(s: Seq<char>) -> Seq<char>
  decreases s.len()
{
    if s.len() == 0 {
        s
    } else if s[0] == '0' {
        strip_leading(s.subrange(1, s.len() as int))
    } else {
        s
    }
}

proof fn strip_leading_preserves_value(s: Seq<char>)
  requires valid_bit_string(s)
  ensures str2int(s) == str2int(strip_leading(s))
  decreases s.len()
{
  if s.len() == 0 {
  } else {
    if s[0] == '0' {
      let t = s.subrange(1, s.len() as int);
      strip_leading_preserves_value(t);
      // After removing a leading '0', the interpreted numeric value is preserved
      // We rely on the recursive definition of str2int and the recursive proof above
      assert(str2int(strip_leading(s)) == str2int(strip_leading(t)));
      assert(str2int(s) == str2int(strip_leading(s)));
    } else {
      assert(strip_leading(s) == s);
      assert(str2int(s) == str2int(strip_leading(s)));
    }
  }
}

proof fn compare_equal_bits_recursive(ss1: Seq<char>, ss2: Seq<char>, i: int, len: int, s1orig: Seq<char>, s2orig: Seq<char>, res: i32)
  requires valid_bit_string(ss1) && valid_bit_string(ss2),
           0 <= i <= len,
           len == ss1.len(),
           len == ss2.len()
  decreases len - i
{
  if i == len {
    // all bits equal
    assert(str2int(s1orig) == str2int(s2orig));
    assert(res == 0);
  } else {
    if ss1[i] != ss2[i] {
      if ss1[i] == '0' {
        assert(str2int(s1orig) < str2int(s2orig));
        assert(res == -1);
      } else {
        assert(str2int(s1orig) > str2int(s2orig));
        assert(res == 1);
      }
    } else {
      // proceed to next index
      compare_equal_bits_recursive(ss1, ss2, i + 1, len, s1orig, s2orig, res);
    }
  }
}

proof fn compare_spec_correct(s1: Vec<char>, s2: Vec<char>, res: i32)
  requires valid_bit_string(s1@) && valid_bit_string(s2@)
  ensures 
    str2int(s1@) < str2int(s2@) ==> res == -1,
    str2int(s1@) == str2int(s2@) ==> res == 0,
    str2int(s1@) > str2int(s2@) ==> res == 1
{
  let ss1 = strip_leading(s1@);
  let ss2 = strip_leading(s2@);
  strip_leading_preserves_value(s1@);
  strip_leading_preserves_value(s2@);

  if ss1.len() == 0 && ss2.len() == 0 {
    assert(str2int(s1@) == str2int(s2@));
    assert(res == 0);
  } else if ss1.len() < ss2.len() {
    assert(str2int(s1@) < str2int(s2@));
    assert(res == -1);
  } else if ss1.len() > ss2.len() {
    assert(str2int(s1@) > str2int(s2@));
    assert(res == 1);
  } else {
    let len: int = ss1.len() as int;
    if len == 0 {
      assert(res == 0);
    } else {
      // compare bits from most significant to least
      compare_equal_bits_recursive(ss1, ss2, 0, len, s1@, s2@, res);
    }
  }
}

// </vc-helpers>

// <vc-spec>
fn compare(s1: Vec<char>, s2: Vec<char>) -> (res: i32)
  requires valid_bit_string(s1@) && valid_bit_string(s2@)
  ensures 
    str2int(s1@) < str2int(s2@) ==> res == -1,
    str2int(s1@) == str2int(s2@) ==> res == 0,
    str2int(s1@) > str2int(s2@) ==> res == 1
  decreases str2int(s1@) + str2int(s2@)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 9): strip leading zeros and compare effective lengths and bits */
  let mut i1: usize = 0;
  while i1 < s1.len() && s1[i1] == '0'
      invariant i1 <= s1.len(),
      decreases s1.len() - i1
  {
    i1 += 1;
  }

  let mut i2: usize = 0;
  while i2 < s2.len() && s2[i2] == '0'
      invariant i2 <= s2.len(),
      decreases s2.len() - i2
  {
    i2 += 1;
  }

  let eff1: usize = s1.len() - i1;
  let eff2: usize = s2.len() - i2;

  if eff1 == 0 && eff2 == 0 {
    let res: i32 = 0;
    proof { compare_spec_correct(s1, s2, res); }
    res
  } else if eff1 < eff2 {
    let res: i32 = -1;
    proof { compare_spec_correct(s1, s2, res); }
    res
  } else if eff1 > eff2 {
    let res: i32 = 1;
    proof { compare_spec_correct(s1, s2, res); }
    res
  } else {
    let mut k: usize = 0;
    let mut out: i32 = 0;
    while k < eff1
        invariant k <= eff1,
        decreases eff1 - k
    {
      let b1 = s1[i1 + k];
      let b2 = s2[i2 + k];
      if b1 != b2 {
        if b1 == '0' {
          out = -1;
        } else {
          out = 1;
        }
        break;
      }
      k += 1;
    }
    let res: i32 = out;
    proof { compare_spec_correct(s1, s2, res); }
    res
  }
}

// </vc-code>


}

fn main() {}