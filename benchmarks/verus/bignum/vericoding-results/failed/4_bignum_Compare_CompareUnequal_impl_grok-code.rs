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
/* helper modified by LLM (iteration 10): named return value in function signature to fix compilation error in ensures clause */
spec fn compute_value_spec(s: Seq<char>) -> nat
    recommends valid_bit_string(s)
    decreases s.len()
{
    if s.len() == 0 {
        0nat
    } else {
        2nat * compute_value_spec(s.subrange(0, s.len() - 1)) + 
        (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
    }
}

proof fn lemma_compute_value_spec_equiv_str2int(s: Seq<char>)
    requires valid_bit_string(s)
    ensures compute_value_spec(s) == str2int(s)
    decreases s.len()
{
    if s.len() != 0 {
        lemma_compute_value_spec_equiv_str2int(s.subrange(0, s.len() - 1));
    }
}

fn compute_value_exec(s: &Vec<char>) -> (result: u64)
    requires
        valid_bit_string(s@),
        s@.len() < 64
    ensures
        compute_value_spec(s@) == result as nat
{
    let mut result = 0u64;
    let mut i: usize = 0;
    proof {
        assert(s.len() as nat == s@.len());
    }
    while i < s.len()
        invariant
            i as nat <= s@.len(),
            result as nat == compute_value_spec(s@.subrange(0, i as int))
        decreases (s.len() - i) as nat
    {
        result = result * 2 + if s[i] == '1' { 1 } else { 0 };
        i += 1;
    }
    result
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
  /* code modified by LLM (iteration 10): maintained logic intact for comparison via exec values with proofs */
  proof {
    lemma_compute_value_spec_equiv_str2int(s1@);
    lemma_compute_value_spec_equiv_str2int(s2@);
  }
  let a = compute_value_exec(&s1);
  let b = compute_value_exec(&s2);
  let res = if a < b {
    -1
  } else if a > b {
    1
  } else {
    0
  };
  proof {
    if res == -1 {
      assert(str2int(s1@) == compute_value_spec(s1@));
      assert(str2int(s2@) == compute_value_spec(s2@));
      assert(str2int(s1@) < str2int(s2@));
    } else if res == 1 {
      assert(str2int(s1@) == compute_value_spec(s1@));
      assert(str2int(s2@) == compute_value_spec(s2@));
      assert(str2int(s1@) > str2int(s2@));
    } else {
      assert(str2int(s1@) == compute_value_spec(s1@));
      assert(str2int(s2@) == compute_value_spec(s2@));
      assert(str2int(s1@) == str2int(s2@));
    }
  }
  res
}
// </vc-code>


}

fn main() {}