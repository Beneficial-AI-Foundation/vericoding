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
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
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
fn remove_leading_zeros(v: Vec<char>) -> (res: Vec<char>)
    requires valid_bit_string(v@)
    ensures valid_bit_string(res@) && str2int(res@) == str2int(v@) && res.len() > 0 && (res.len() > 1 ==> res[0] != '0')
{
    let mut i = 0;
    let n = v.len();
    while i < n && v[i] == '0' {
        i += 1;
    }
    if i == n {
        vec!['0']
    } else {
        let mut res = Vec::new();
        for j in i..n {
            res.push(v[j]);
        }
        res
    }
}

fn reverse_vec(v: Vec<char>) -> Vec<char> {
    let mut res = Vec::new();
    for i in (0..v.len()).rev() {
        res.push(v[i]);
    }
    res
}
// </vc-helpers>

// <vc-spec>
fn sub(s1: Vec<char>, s2: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(s1@) && valid_bit_string(s2@) &&
    str2int(s1@) >= str2int(s2@)
  ensures 
    valid_bit_string(res@) &&
    str2int(res@) == str2int(s1@) - str2int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 2): fixed compilation errors by using usize indices and adjusting loop */
    let mut result = Vec::new();
    let mut borrow = 0;
    let mut i = s1.len();
    let mut j = s2.len();

    while i > 0 || j > 0 || borrow != 0 {
        let bit1 = if i > 0 { s1[i-1] } else { '0' };
        let bit2 = if j > 0 { s2[j-1] } else { '0' };

        let b1 = if bit1 == '1' { 1 } else { 0 };
        let b2 = if bit2 == '1' { 1 } else { 0 };

        let diff = b1 - b2 - borrow;
        if diff < 0 {
            borrow = 1;
            result.push(if diff + 2 == 1 { '1' } else { '0' });
        } else {
            borrow = 0;
            result.push(if diff == 1 { '1' } else { '0' });
        }

        if i > 0 { i -= 1; }
        if j > 0 { j -= 1; }
    }

    let mut normalized_result = reverse_vec(result);
    normalized_result = remove_leading_zeros(normalized_result);
    normalized_result
}
// </vc-code>


}

fn main() {}