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
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

fn sub(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2),
    str2int(s1) >= str2int(s2)
  ensures 
    valid_bit_string(res),
    str2int(res) == str2int(s1) - str2int(s2)
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 7): conversion helpers between Vec<char> and usize-based integers */
fn int_of_vec(v: &Vec<char>) -> usize {
    let mut res: usize = 0usize;
    let mut idx: usize = 0usize;
    while idx < v.len()
        invariant
            idx <= v.len(),
            // res is bounded by 2^idx - 1 after processing idx bits (approximate bound to help verification)
            res <= (1usize << idx),
        decreases v.len() - idx
    {
        let c = v[idx];
        if c == '1' {
            res = res * 2 + 1;
        } else {
            res = res * 2;
        }
        idx += 1usize;
    }
    res
}

/* helper modified by LLM (iteration 7): convert usize to Vec<char> (binary) with loop invariants for reversing */
fn vec_of_int(mut n: usize) -> Vec<char> {
    let mut bits: Vec<char> = Vec::new();
    if n == 0usize {
        bits.push('0');
    } else {
        while n > 0usize
            invariant
                n >= 0usize,
            decreases n
        {
            let b = if n % 2usize == 1usize { '1' } else { '0' };
            bits.push(b);
            n = n / 2usize;
        }
        let mut i: usize = 0usize;
        if bits.len() > 0usize {
            let mut j: usize = bits.len() - 1usize;
            while i < j
                invariant
                    i <= j,
                    j < bits.len(),
                    i < bits.len(),
                decreases j - i
            {
                let tmp = bits[i];
                bits[i] = bits[j];
                bits[j] = tmp;
                i += 1usize;
                j -= 1usize;
            }
        }
    }
    bits
}

// </vc-helpers>

// <vc-spec>
fn div_mod(dividend: Vec<char>, divisor: Vec<char>) -> (result: (Vec<char>, Vec<char>))
  requires 
    valid_bit_string(dividend@) && valid_bit_string(divisor@),
    str2int(divisor@) > 0
  ensures 
    valid_bit_string(result.0@) && valid_bit_string(result.1@),
    str2int(result.0@) == str2int(dividend@) / str2int(divisor@),
    str2int(result.1@) == str2int(dividend@) % str2int(divisor@)
// </vc-spec>
// <vc-code>
{
/* code modified by LLM (iteration 7): compute quotient and remainder using usize helpers with loop invariants */
    let divisor_val = int_of_vec(&divisor);
    let mut rem = int_of_vec(&dividend);
    let mut q: usize = 0usize;
    while rem >= divisor_val
        invariant
            rem >= 0usize,
            // q does not grow faster than rem (simple conservative bound)
            q <= rem + 1usize,
        decreases rem
    {
        rem = rem - divisor_val;
        q = q + 1usize;
    }
    let qv = vec_of_int(q);
    let rv = vec_of_int(rem);
    (qv, rv)
}

// </vc-code>


}

fn main() {}