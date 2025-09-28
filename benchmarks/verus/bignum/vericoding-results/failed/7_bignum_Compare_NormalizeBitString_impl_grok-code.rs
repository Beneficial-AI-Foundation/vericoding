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
/* helper modified by LLM (iteration 4): replaced s.is_empty() with s.len() == 0 to fix unsupported method compilation error */
fn exec_normalize(s: Vec<char>) -> (result: Vec<char>)
  requires valid_bit_string(s@)
  ensures
      valid_bit_string(result@),
      result.len() > 0,
      (result.len() > 1 ==> result[0] != '0'),
      (valid_bit_string(s@) ==> str2int(s@) == str2int(result@))
{
  /* helper modified by LLM (iteration 3): fixed sequence indexing using as int and subrange */
  if s.len() == 0 {
    return vec!['0'];
  }
  let mut i: usize = 0;
  while i < s.len()
      invariant
          0 <= i <= s.len(),
          forall|j: int| 0 <= j < i ==> s@[j] == '0',
          valid_bit_string(s@)
      decreases s.len() - i
  {
    if s[i] == '0' {
      i += 1;
    } else {
      break;
    }
  }
  if i == s.len() {
    return vec!['0'];
  }
  let mut result_vec = Vec::new();
  let mut j: usize = i;
  while j < s.len()
      invariant
          i <= j <= s.len(),
          result_vec.len() == j - i,
          result_vec@ == s@.subrange(i as int, j as int),
          valid_bit_string(s@),
          s@[i as int] != '0'
      decreases s.len() - j
  {
    result_vec.push(s[j]);
    j += 1;
  }
  proof { assert(str2int(s@) == str2int(result_vec@)); }
  return result_vec;
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
    /* code modified by LLM (iteration 4): unchanged from previous iteration */
    let n1 = exec_normalize(s1);
    let n2 = exec_normalize(s2);
    let res = if n1.len() == 1 && n1[0] == '0' {
        if n2.len() == 1 && n2[0] == '0' {
            0i8
        } else {
            -1i8
        }
    } else if n2.len() == 1 && n2[0] == '0' {
        1i8
    } else if n1.len() > n2.len() {
        1i8
    } else if n1.len() < n2.len() {
        -1i8
    } else {
        let mut res = 0i8;
        let mut k = 0;
        while k < n1.len()
            invariant
                0 <= k <= n1.len(),
                forall|i: int| 0 <= i < k ==> n1@[i] == n2@[i]
            decreases n1.len() - k
        {
            if n1[k] > n2[k] {
                res = 1i8;
                break;
            } else if n1[k] < n2[k] {
                res = -1i8;
                break;
            }
            k += 1;
        }
        res
    };
    return res;
}
// </vc-code>


}

fn main() {}