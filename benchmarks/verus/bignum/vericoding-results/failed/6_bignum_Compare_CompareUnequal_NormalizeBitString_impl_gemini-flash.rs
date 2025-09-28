// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn str2int(s: Seq<char>) -> nat
  recommends valid_bit_string(s)
  decreases s.len()
{
  if s.len() == 0 { 0nat } else { 2nat * str2int(s.subrange(0, s.len() - 1 as int)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

fn normalize_bit_string(s: Seq<char>) -> (t: Seq<char>)
  ensures
    valid_bit_string(t),
    t.len() > 0,
    t.len() > 1 ==> t[0] != '0',
    valid_bit_string(s) ==> str2int(s) == str2int(t),
{
  assume(false);
  unreached()
}

fn compare_unequal(s1: Seq<char>, s2: Seq<char>) -> (res: i32)
  requires
    valid_bit_string(s1) && valid_bit_string(s2),
    s1.len() > 0,
    s1.len() > 1 ==> s1[0] != '0',
    s2.len() > 0,
    s2.len() > 1 ==> s2[0] != '0',
    s1.len() > s2.len(),
  ensures
    str2int(s1) < str2int(s2) ==> res == -1,
    str2int(s1) == str2int(s2) ==> res == 0,
    str2int(s1) > str2int(s2) ==> res == 1,
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Removed `nat` cast for index `i` in executable code for `Seq` access, using `i` directly as `usize` */
fn do_compare_normalized(s1: Seq<char>, s2: Seq<char>) -> (res: i32)
  requires
    valid_bit_string(s1) && valid_bit_string(s2),
    s1.len() > 0,
    s1.len() > 1 ==> s1[0] != '0',
    s2.len() > 0,
    s2.len() > 1 ==> s2[0] != '0',
  ensures
    str2int(s1) < str2int(s2) ==> res == -1,
    str2int(s1) == str2int(s2) ==> res == 0,
    str2int(s1) > str2int(s2) ==> res == 1,
{
    if s1.len() > s2.len() {
        1
    } else if s1.len() < s2.len() {
        -1
    } else {
        let mut i: usize = 0;
        while i < s1.len() as usize
            invariant
                0 <= i,
                i <= s1.len(),
                s1.len() == s2.len(),
                forall|j: int| 0 <= j < i ==> s1[j as int] == s2[j as int] // Added as int to j
            decreases s1.len() - i
        {
            if s1[i as int] == '0' && s2[i as int] == '1' {
                return -1;
            } else if s1[i as int] == '1' && s2[i as int] == '0' {
                return 1;
            }
            i = i + 1;
        }
        0
    }
}
// </vc-helpers>

// <vc-spec>
fn compare(s1: Vec<char>, s2: Vec<char>) -> (res: i32)
  requires valid_bit_string(s1@) && valid_bit_string(s2@)
  ensures
    str2int(s1@) < str2int(s2@) ==> res == -1,
    str2int(s1@) == str2int(s2@) ==> res == 0,
    str2int(s1@) > str2int(s2@) ==> res == 1,
  decreases str2int(s1@) + str2int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Calls `do_compare_normalized` with results from `normalize_bit_string`. */
{
  let n_s1 = normalize_bit_string(s1@);
  let n_s2 = normalize_bit_string(s2@);
  do_compare_normalized(n_s1, n_s2)
}
// </vc-code>


}

fn main() {}