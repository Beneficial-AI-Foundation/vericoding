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
    2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
  }
}

spec fn valid_bit_string(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_str2int_leading_zeros(s: Seq<char>, s_no_leading_zeros: Seq<char>)
  requires valid_bit_string(s) && valid_bit_string(s_no_leading_zeros)
  requires s_no_leading_zeros.len() > 0 && (s_no_leading_zeros.len() == 1 || s_no_leading_zeros[0] != '0')
  requires s.len() > s_no_leading_zeros.len()
  ensures str2int(s) < str2int(s_no_leading_zeros)
{
  if s.len() == s_no_leading_zeros.len() + 1 {
    assert(s[0] == '0');
    calc! {
      str2int(s);
      2 * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1 } else { 0 });
      2 * str2int(s_no_leading_zeros) + (if s[s.len() - 1] == '1' { 1 } else { 0 });
      == { assert(s.subrange(0, s.len() - 1) == s_no_leading_zeros); }
      2 * str2int(s_no_leading_zeros) + (if s[s.len() - 1] == '1' { 1 } else { 0 });
      <= 2 * str2int(s_no_leading_zeros) + 1;
      < 2 * str2int(s_no_leading_zeros) + 2;
      <= 2 * str2int(s_no_leading_zeros) + str2int(s_no_leading_zeros);
      == { assert(str2int(s_no_leading_zeros) >= 1); }
      3 * str2int(s_no_leading_zeros);
      <= 2 * str2int(s_no_leading_zeros) + str2int(s_no_leading_zeros) * (s_no_leading_zeros.len() as nat);
      == { lemma_str2int_bound(s_no_leading_zeros); }
      str2int(s_no_leading_zeros) + str2int(s_no_leading_zeros) * (s_no_leading_zeros.len() as nat);
      == str2int(s_no_leading_zeros) * (1 + (s_no_leading_zeros.len() as nat));
      <= str2int(s_no_leading_zeros) * (2 * (s_no_leading_zeros.len() as nat));
    }
  } else {
    lemma_str2int_leading_zeros(s.subrange(0, s.len() - 1), s_no_leading_zeros);
    calc! {
      str2int(s);
      2 * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1 } else { 0 });
      < 2 * str2int(s_no_leading_zeros) + (if s[s.len() - 1] == '1' { 1 } else { 0 });
      <= 2 * str2int(s_no_leading_zeros) + 1;
      < 2 * str2int(s_no_leading_zeros) + 2;
      <= 2 * str2int(s_no_leading_zeros) + str2int(s_no_leading_zeros);
      == { assert(str2int(s_no_leading_zeros) >= 1); }
      3 * str2int(s_no_leading_zeros);
    }
  }
}

proof fn lemma_str2int_bound(s: Seq<char>)
  requires valid_bit_string(s)
  ensures str2int(s) <= (2 as nat).pow(s.len() as int) - 1
{
  if s.len() == 0 {
  } else {
    lemma_str2int_bound(s.subrange(0, s.len() - 1));
    calc! {
      str2int(s);
      2 * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1 } else { 0 });
      <= 2 * ((2 as nat).pow((s.len() - 1) as int) - 1) + 1;
      == 2 * (2 as nat).pow((s.len() - 1) as int) - 2 + 1;
      == (2 as nat).pow(s.len() as int) - 1;
    }
  }
}
// </vc-helpers>

// <vc-spec>
fn compare_unequal(s1: Vec<char>, s2: Vec<char>) -> (res: i32)
  requires 
    valid_bit_string(s1@) && valid_bit_string(s2@),
    s1@.len() > 0,
    s1@.len() > 1 ==> s1@[0] != '0',
    s2@.len() > 0,
    s2@.len() > 1 ==> s2@[0] != '0',
    s1@.len() > s2@.len()
  ensures 
    str2int(s1@) < str2int(s2@) ==> res == -1,
    str2int(s1@) == str2int(s2@) ==> res == 0,
    str2int(s1@) > str2int(s2@) ==> res == 1
// </vc-spec>
// <vc-code>
{
    let s1_int = str2int(s1@);
    let s2_int = str2int(s2@);
    
    proof {
        lemma_str2int_leading_zeros(s1@, s2@);
    }
    
    if s1_int < s2_int {
        -1
    } else if s1_int == s2_int {
        0
    } else {
        1
    }
}
// </vc-code>


}

fn main() {}