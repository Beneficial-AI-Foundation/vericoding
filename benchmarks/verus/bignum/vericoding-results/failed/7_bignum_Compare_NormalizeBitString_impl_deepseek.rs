// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn str2int(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() == 0 {
      0nat
  } else {
      2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
  }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

fn normalize_bit_string(s: Seq<char>) -> (t: Seq<char>)
  ensures 
      valid_bit_string(t) &&
      t.len() > 0 &&
      (t.len() > 1 ==> t[0] != '0') &&
      (valid_bit_string(s) ==> str2int(s) == str2int(t))
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Fixed type mismatches and added proper type conversions between int and nat */
proof fn lemma_str2int_lt(a: Seq<char>, b: Seq<char>) 
    requires valid_bit_string(a) && valid_bit_string(b) && a.len() > 0 && b.len() > 0,
    ensures if a.len() < b.len() { str2int(a) < str2int(b) } else if b.len() < a.len() { str2int(b) < str2int(a) } else { true }
{
    if a.len() < b.len() {
        proof {
            lemma_str2int_max_for_len(a, (b.len() - 1) as nat);
            assert(str2int(a) <= pow2((b.len() - 1) as nat) - 1);
            assert(str2int(b) >= pow2((b.len() - 1) as nat));
        }
    } else if b.len() < a.len() {
        proof {
            lemma_str2int_max_for_len(b, (a.len() - 1) as nat);
            assert(str2int(b) <= pow2((a.len() - 1) as nat) - 1);
            assert(str2int(a) >= pow2((a.len() - 1) as nat));
        }
    }
}

proof fn lemma_str2int_max_for_len(s: Seq<char>, max_len: nat)
    requires valid_bit_string(s) && s.len() <= max_len,
    ensures str2int(s) <= pow2(max_len) - 1
    decreases s.len()
{
    if s.len() > 0 {
        let sub = s.subrange(0, s.len() - 1);
        lemma_str2int_max_for_len(sub, (max_len - 1) as nat);
        assert(str2int(s) == 2 * str2int(sub) + (if s.index((s.len() - 1) as int) == '1' {1nat} else {0nat}));
        assert(str2int(sub) <= pow2((max_len - 1) as nat) - 1);
        assert(2 * str2int(sub) + (if s.index((s.len() - 1) as int) == '1' {1nat} else {0nat}) <= 2 * (pow2((max_len - 1) as nat) - 1) + 1);
        assert(2 * (pow2((max_len - 1) as nat) - 1) + 1 == pow2(max_len) - 1);
    } else {
        assert(str2int(s) == 0);
        assert(0 <= pow2(max_len) - 1);
    }
}

spec fn pow2(exp: nat) -> nat
    decreases exp
{
    if exp == 0 { 1nat } else { 2nat * pow2((exp - 1) as nat) }
}
// </vc-helpers>

// <vc-spec>
fn compare(s1: Vec<char>, s2: Vec<char>) -> (res: i8)
  requires valid_bit_string(s1@) && valid_bit_string(s2@)
  ensures 
      (str2int(s1@) < str2int(s2@) ==> res as int == -1) &&
      (str2int(s1@) == str2int(s2@) ==> res as int == 0) &&
      (str2int(s1@) > str2int(s2@) ==> res as int == 1)
  decreases str2int(s1@) + str2int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): Fixed type mismatches using proper usize conversion and while loop counter */
    let a_norm = normalize_bit_string(s1@);
    let b_norm = normalize_bit_string(s2@);
    
    if a_norm.len() < b_norm.len() {
        proof { lemma_str2int_lt(a_norm, b_norm); }
        -1
    } else if b_norm.len() < a_norm.len() {
        proof { lemma_str2int_lt(b_norm, a_norm); }
        1
    } else {
        let mut i: usize = 0;
        let len = a_norm.len() as usize;
        while i < len
            invariant 
                0 <= i <= len,
                forall|j: int| 0 <= j < i as int ==> a_norm.index(j) == b_norm.index(j),
                valid_bit_string(a_norm) && valid_bit_string(b_norm)
        {
            if a_norm.index(i as int) < b_norm.index(i as int) {
                return -1;
            } else if a_norm.index(i as int) > b_norm.index(i as int) {
                return 1;
            }
            i = i + 1;
        }
        0
    }
}
// </vc-code>


}

fn main() {}