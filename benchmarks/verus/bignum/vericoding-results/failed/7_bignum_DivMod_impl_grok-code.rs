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
/* helper modified by LLM (iteration 10): changed nat and int types to usize for executable code, handled vector indexing safely */
fn normalize(v: &Vec<char>) -> Vec<char>
{
  let mut i: usize = 0;
  while i < v.len()
      decreases v.len() - i
  {
    if i < v.len() && v[i] == '0' {
      i += 1;
    } else {
      break;
    }
  }
  if i == v.len() {
    vec!['0']
  } else {
    let mut result = Vec::new();
    let mut j: usize = i;
    while j < v.len()
        decreases v.len() - j
    {
      result.push(v[j]);
      j += 1;
    }
    result
  }
}

fn compare_vectors(a: &Vec<char>, b: &Vec<char>) -> i32
{
  let na = normalize(a);
  let nb = normalize(b);
  if na.len() > nb.len() {
    1
  } else if na.len() < nb.len() {
    -1
  } else {
    let mut i: usize = 0;
    while i < na.len()
        decreases na.len() - i
    {
      if na[i] > nb[i] {
        return 1;
      } else if na[i] < nb[i] {
        return -1;
      }
      i += 1;
    }
    0
  }
}

fn subtract_vectors(a: &Vec<char>, b: &Vec<char>) -> Vec<char>
{
  let na = normalize(a);
  let nb = normalize(b);
  let len = na.len();
  let nb_len = nb.len();
  let mut bb = Vec::new();
  let mut temp: usize = 0;
  let diff = len - nb_len;
  while temp < diff
      decreases diff - temp
  {
    bb.push('0');
    temp += 1;
  }
  let mut idx: usize = 0;
  while idx < nb_len
      decreases nb_len - idx
  {
    bb.push(nb[idx]);
    idx += 1;
  }
  let mut result = Vec::new();
  let mut carry = 0i64;
  let mut pos: usize = 0;
  while pos < len
      decreases len - pos
  {
    let va = (na[len - 1 - pos] as i64 - '0' as i64);
    let vb = (bb[len - 1 - pos] as i64 - '0' as i64);
    let sub = va - vb - carry;
    if sub < 0 {
      let ch = ('0' as i64 + sub + 10) as u8 as char;
      result.push(ch);
      carry = 1;
    } else {
      let ch = ('0' as i64 + sub) as u8 as char;
      result.push(ch);
      carry = 0;
    }
    pos += 1;
  }
  result.reverse();
  normalize(&result)
}
// </vc-helpers>

// <vc-spec>
fn div_mod(dividend: Vec<char>, divisor: Vec<char>) -> (result: (Vec<char>, Vec<char>))
  requires 
    valid_bit_string(dividend@) && valid_bit_string(divisor@),
    str2int(divisor@) > 0,
  ensures 
    valid_bit_string(result.0@) && valid_bit_string(result.1@),
    str2int(result.0@) == str2int(dividend@) / str2int(divisor@),
    str2int(result.1@) == str2int(dividend@) % str2int(divisor@),
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): replaced nat and int with usize, used direct indexing for vector assignment */
{
    let d = normalize(&dividend);
    let ds = normalize(&divisor);
    let mut q = Vec::new();
    let mut r = Vec::new();
    if compare_vectors(&d, &ds) < 0 {
        q = vec!['0'];
        r = d.clone();
    } else {
        let k: usize = d.len() - ds.len();
        let mut temp: usize = 0;
        while temp <= k
            decreases k - temp
        {
            q.push('0');
            temp += 1;
        }
        r = d.clone();
        let mut i: usize = 0;
        while i <= k
            decreases k - i
        {
            let s: usize = k - i;
            let mut shifted_b = ds.clone();
            let mut shift_count: usize = 0;
            while shift_count < s
                decreases s - shift_count
            {
                shifted_b.push('0');
                shift_count += 1;
            }
            if compare_vectors(&r, &shifted_b) >= 0 {
                r = subtract_vectors(&r, &shifted_b);
                q[i] = '1';
            }
            i += 1;
        }
        q = normalize(&q);
        r = normalize(&r);
    }
    (q, r)
}
// </vc-code>


}

fn main() {}