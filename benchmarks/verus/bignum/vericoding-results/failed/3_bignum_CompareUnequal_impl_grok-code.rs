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
/* helper modified by LLM (iteration 8): changed int to usize for executable code, adjusted invariants and casts */
fn str2int_exec(s: Vec<char>) -> (result: u64)
    requires
        valid_bit_string(s@),
        s@.len() < 64
    ensures
        result as nat == str2int(s@)
{
    let mut result: u64 = 0;
    let mut i: usize = 0;
    let slen = s.len();
    while i < slen
        invariant
            0 <= i,
            i as int <= slen as int,
            result as nat == str2int(s@.subrange(0, i as int))
        decreases slen - i
    {
        result = result * 2 + if s[i] == '1' { 1u64 } else { 0u64 };
        i += 1;
    }
    result
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
/* code modified by LLM (iteration 8): main logic unchanged as spec ensures res==1 */
{
    1
}
// </vc-code>


}

fn main() {}