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
/* helper modified by LLM (iteration 10): use nat for pow2 index to match Seq.len() and adjust proofs */
spec fn pow2(n: nat) -> nat
  decreases n
{
  if n == 0 {
    1nat
  } else {
    2nat * pow2(n - 1)
  }
}

proof fn pow2_mono(a: nat, b: nat)
  requires
    a >= b
  ensures
    pow2(a) >= pow2(b)
  decreases a
{
  if a == b {
    proof { assert(pow2(a) == pow2(b)); }
  } else {
    pow2_mono(a - 1, b);
    proof {
      assert(pow2(a) == 2nat * pow2(a - 1));
      assert(pow2(a - 1) >= pow2(b));
      assert(2nat * pow2(a - 1) >= pow2(b));
      assert(pow2(a) >= pow2(b));
    }
  }
}

proof fn str2int_upper_bound(s: Seq<char>)
  requires
    valid_bit_string(s)
  ensures
    str2int(s) <= pow2(s.len()) - 1nat
  decreases s.len()
{
  if s.len() == 0 {
    proof {
      assert(str2int(s) == 0nat);
      assert(pow2(s.len()) == 1nat);
      assert(pow2(s.len()) - 1nat == 0nat);
      assert(str2int(s) <= pow2(s.len()) - 1nat);
    }
  } else {
    let p = s.subrange(0, s.len() - 1);
    str2int_upper_bound(p);
    proof {
      assert(str2int(s) == 2nat * str2int(p) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }));
      assert(str2int(p) <= pow2(p.len()) - 1nat);
      assert(2nat * str2int(p) <= 2nat * (pow2(p.len()) - 1nat));
      assert((if s[s.len() - 1] == '1' { 1nat } else { 0nat }) <= 1nat);
      assert(2nat * (pow2(p.len()) - 1nat) + 1nat == 2nat * pow2(p.len()) - 1nat);
      assert(2nat * pow2(p.len()) == pow2(s.len()));
      assert(2nat * pow2(p.len()) - 1nat == pow2(s.len()) - 1nat);
      assert(2nat * str2int(p) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }) <= pow2(s.len()) - 1nat);
      assert(str2int(s) <= pow2(s.len()) - 1nat);
    }
  }
}

proof fn str2int_lower_bound_nonleading(s: Seq<char>)
  requires
    valid_bit_string(s),
    s.len() > 1,
    s[0] != '0'
  ensures
    str2int(s) >= pow2(s.len() - 1)
  decreases s.len()
{
  if s.len() == 2 {
    let p = s.subrange(0, 1);
    proof {
      assert(p[0] == '1');
      assert(str2int(p) == 1nat);
      assert(str2int(s) == 2nat * str2int(p) + (if s[1] == '1' { 1nat } else { 0nat }));
      assert(str2int(s) >= 2nat * 1nat);
      assert(2nat * 1nat == pow2(1));
      assert(str2int(s) >= pow2(1));
    }
  } else {
    let p = s.subrange(0, s.len() - 1);
    str2int_lower_bound_nonleading(p);
    proof {
      assert(str2int(s) == 2nat * str2int(p) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }));
      assert(str2int(p) >= pow2(p.len() - 1));
      assert(2nat * str2int(p) >= 2nat * pow2(p.len() - 1));
      assert(2nat * pow2(p.len() - 1) == pow2(s.len() - 1));
      assert(str2int(s) >= pow2(s.len() - 1));
    }
  }
}

proof fn compare_length_implies_greater(s1: Seq<char>, s2: Seq<char>)
  requires
    valid_bit_string(s1),
    s1.len() > 0,
    s1.len() > 1 ==> s1[0] != '0',
    valid_bit_string(s2),
    s2.len() > 0,
    s2.len() > 1 ==> s2[0] != '0',
    s1.len() > s2.len()
  ensures
    str2int(s1) > str2int(s2)
  decreases s1.len()
{
  str2int_lower_bound_nonleading(s1);
  str2int_upper_bound(s2);
  pow2_mono(s1.len() - 1, s2.len());

  proof {
    assert(str2int(s1) >= pow2(s1.len() - 1));
    assert(pow2(s1.len() - 1) >= pow2(s2.len()));
    assert(pow2(s2.len()) > pow2(s2.len()) - 1nat);
    assert(pow2(s2.len()) - 1nat >= str2int(s2));
    assert(str2int(s1) > str2int(s2));
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
  /* code modified by LLM (iteration 10): prove s1 > s2 from length and return 1 */
  proof {
    compare_length_implies_greater(s1@, s2@);
  }
  1
}

// </vc-code>


}

fn main() {}