// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
  recommends valid_bit_string(s)
  decreases s.len()
{
  if s.len() == 0 { 0nat } else { 2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
}

fn compare(s1: Seq<char>, s2: Seq<char>) -> (res: i32)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2)
  ensures 
    str2int(s1) < str2int(s2) ==> res == -1,
    str2int(s1) == str2int(s2) ==> res == 0,
    str2int(s1) > str2int(s2) ==> res == 1
  decreases str2int(s1) + str2int(s2)
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 9): vector utilities for bitwise division (normalize, compare, subtract, shift-and-append) */
fn normalize(v: &Vec<char>) -> Vec<char> {
    let mut i: usize = 0;
    while i < v.len() && v[i] == '0'
        invariant i <= v.len(),
        decreases v.len() - i
    {
        i += 1;
    }
    let mut res: Vec<char> = Vec::new();
    if i == v.len() {
        res.push('0');
    } else {
        let mut k: usize = i;
        while k < v.len()
            invariant k <= v.len(),
            decreases v.len() - k
        {
            res.push(v[k]);
            k += 1;
        }
    }
    res
}

fn shift_left_append(r: &Vec<char>, bit: char) -> Vec<char> {
    let mut res: Vec<char> = Vec::new();
    let mut i: usize = 0;
    while i < r.len()
        invariant i <= r.len(),
        decreases r.len() - i
    {
        res.push(r[i]);
        i += 1;
    }
    res.push(bit);
    res
}

fn cmp_vec(a: &Vec<char>, b: &Vec<char>) -> i32 {
    let aa = normalize(a);
    let bb = normalize(b);
    if aa.len() < bb.len() { return -1; }
    if aa.len() > bb.len() { return 1; }
    let mut i: usize = 0;
    while i < aa.len()
        invariant i <= aa.len(),
        decreases aa.len() - i
    {
        if aa[i] < bb[i] { return -1; }
        if aa[i] > bb[i] { return 1; }
        i += 1;
    }
    0
}

fn sub_vec(a: &Vec<char>, b: &Vec<char>) -> Vec<char> {
    // subtract b from a (a >= b assumed); both are MSB-first bit vectors
    let la = a.len();
    let lb = b.len();
    let mut pos: usize = 0;
    let mut borrow: i32 = 0;
    let mut rev: Vec<char> = Vec::new();
    while pos < la
        invariant pos <= la,
        decreases la - pos
    {
        let ai = a[la - 1 - pos];
        let bi = if pos < lb { b[lb - 1 - pos] } else { '0' };
        let ai_v = if ai == '1' { 1 } else { 0 };
        let bi_v = if bi == '1' { 1 } else { 0 };
        let mut diff: i32 = ai_v - bi_v - borrow;
        if diff < 0 {
            diff += 2;
            borrow = 1;
        } else {
            borrow = 0;
        }
        if diff == 1 { rev.push('1'); } else { rev.push('0'); }
        pos += 1;
    }
    // reverse and remove leading zeros
    let mut start: usize = rev.len();
    while start > 0 && rev[start - 1] == '0'
        invariant start <= rev.len(),
        decreases start
    {
        start -= 1;
    }
    let mut res: Vec<char> = Vec::new();
    if start == 0 {
        res.push('0');
    } else {
        let mut idx: usize = start;
        while idx > 0
            invariant idx <= start,
            decreases idx
        {
            res.push(rev[idx - 1]);
            idx -= 1;
        }
    }
    res
}

// </vc-helpers>

// <vc-spec>
fn div_mod(dividend: Vec<char>, divisor: Vec<char>) -> (res: (Vec<char>, Vec<char>))
  requires 
    valid_bit_string(dividend@) && valid_bit_string(divisor@),
    str2int(divisor@) > 0
  ensures 
    valid_bit_string(res.0@) && valid_bit_string(res.1@),
    str2int(res.0@) == str2int(dividend@) / str2int(divisor@),
    str2int(res.1@) == str2int(dividend@) % str2int(divisor@)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 9): implement long division on bit vectors using helper utilities */
  // normalize inputs
  let dvd = normalize(&dividend);
  let dvs = normalize(&divisor);

  // initialize remainder (start at zero) and quotient accumulator
  let mut rem: Vec<char> = Vec::new();
  rem.push('0');
  let mut qacc: Vec<char> = Vec::new();

  let mut i: usize = 0;
  while i < dvd.len()
      invariant
          i <= dvd.len(),
      decreases dvd.len() - i
  {
      // shift rem left and append current bit
      rem = shift_left_append(&rem, dvd[i]);
      rem = normalize(&rem);

      if cmp_vec(&rem, &dvs) >= 0 {
          rem = sub_vec(&rem, &dvs);
          qacc.push('1');
      } else {
          qacc.push('0');
      }

      i += 1;
  }

  let qres = normalize(&qacc);
  let rres = normalize(&rem);

  (qres, rres)
}

// </vc-code>


}

fn main() {}