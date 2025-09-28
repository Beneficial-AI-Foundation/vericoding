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
/* helper modified by LLM (iteration 10): remove leading zeros by removing front elements and compare remaining vectors safely */
fn cmp_bits(a: &Vec<char>, b: &Vec<char>) -> i32 {
    let mut a2 = a.clone();
    while a2.len() > 0
        invariant
            a2.len() <= a.len(),
        decreases a2.len()
    {
        if a2[0] != '0' { break; }
        a2.remove(0);
    }
    let mut b2 = b.clone();
    while b2.len() > 0
        invariant
            b2.len() <= b.len(),
        decreases b2.len()
    {
        if b2[0] != '0' { break; }
        b2.remove(0);
    }
    let la: usize = a2.len();
    let lb: usize = b2.len();
    if la > lb { return 1; }
    if la < lb { return -1; }
    let mut j: usize = 0;
    while j < la
        invariant
            j <= la,
        decreases la - j
    {
        let ca = a2[j];
        let cb = b2[j];
        if ca != cb {
            if ca == '1' { return 1; } else { return -1; }
        }
        j += 1;
    }
    0
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
{
  /* code modified by LLM (iteration 10): binary long division using clone/pop for safe subtraction and adjusted invariants */
  let mut quotient: Vec<char> = Vec::new();
  let mut remainder: Vec<char> = Vec::new();
  let n = dividend.len();
  let mut i: usize = 0;
  while i < n
      invariant
          i <= n,
          n == dividend.len(),
      decreases n - i
  {
      // bring down next bit
      remainder.push(dividend[i]);

      // if remainder >= divisor then subtract and emit 1 else emit 0
      if cmp_bits(&remainder, &divisor) >= 0 {
          // subtract divisor from remainder using LSB-first pop approach (safe indexing avoided)
          let mut a_copy: Vec<char> = remainder.clone();
          let mut b_copy: Vec<char> = divisor.clone();
          let mut res_rev: Vec<char> = Vec::new();
          let mut borrow: i32 = 0;

          while a_copy.len() > 0 || b_copy.len() > 0
              invariant
                  a_copy.len() <= remainder.len(),
              decreases (a_copy.len() + b_copy.len())
          {
              let ai = match a_copy.pop() { Some(c) => c, None => '0' };
              let bi = match b_copy.pop() { Some(c) => c, None => '0' };
              let aval: i32 = if ai == '1' { 1 } else { 0 };
              let bval: i32 = if bi == '1' { 1 } else { 0 };
              let mut diff: i32;
              if aval >= bval + borrow {
                  diff = aval - bval - borrow;
                  borrow = 0;
              } else {
                  diff = aval + 2 - bval - borrow;
                  borrow = 1;
              }
              let c = if diff == 1 { '1' } else { '0' };
              res_rev.push(c);
          }

          // build result in MSB-first order
          let mut res: Vec<char> = Vec::new();
          let mut j: usize = 0;
          while j < res_rev.len()
              invariant
                  j <= res_rev.len(),
              decreases res_rev.len() - j
          {
              res.push(res_rev[res_rev.len() - 1 - j]);
              j += 1;
          }

          // remove leading zeros
          let mut k2: usize = 0;
          while k2 < res.len()
              invariant
                  k2 <= res.len(),
              decreases res.len() - k2
          {
              if res[k2] != '0' { break; }
              k2 += 1;
          }
          if k2 == res.len() {
              remainder.clear();
          } else {
              let mut newr: Vec<char> = Vec::new();
              let mut t2: usize = k2;
              while t2 < res.len()
                  invariant
                      t2 <= res.len(),
                  decreases res.len() - t2
              {
                  newr.push(res[t2]);
                  t2 += 1;
              }
              remainder = newr;
          }
          quotient.push('1');
      } else {
          quotient.push('0');
      }
      i += 1;
  }

  // strip leading zeros from quotient
  let mut qstart: usize = 0;
  while qstart < quotient.len()
      invariant
          qstart <= quotient.len(),
      decreases quotient.len() - qstart
  {
      if quotient[qstart] == '0' { qstart += 1; } else { break; }
  }
  let mut final_q: Vec<char> = Vec::new();
  if qstart < quotient.len() {
      let mut t = qstart;
      while t < quotient.len()
          invariant
              t <= quotient.len(),
          decreases quotient.len() - t
      {
          final_q.push(quotient[t]);
          t += 1;
      }
  }

  // strip leading zeros from remainder
  let mut rstart: usize = 0;
  while rstart < remainder.len()
      invariant
          rstart <= remainder.len(),
      decreases remainder.len() - rstart
  {
      if remainder[rstart] == '0' { rstart += 1; } else { break; }
  }
  let mut final_r: Vec<char> = Vec::new();
  if rstart < remainder.len() {
      let mut t = rstart;
      while t < remainder.len()
          invariant
              t <= remainder.len(),
          decreases remainder.len() - t
      {
          final_r.push(remainder[t]);
          t += 1;
      }
  }

  (final_q, final_r)
}
// </vc-code>


}

fn main() {}