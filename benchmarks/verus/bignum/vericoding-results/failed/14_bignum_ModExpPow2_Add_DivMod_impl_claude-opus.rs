// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

spec fn str2int(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() == 0 { 
    0nat 
  } else { 
    2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
  }
}

fn add(s1: Seq<char>, s2: Seq<char>) -> (res: Seq<char>)
  requires 
    valid_bit_string(s1) && valid_bit_string(s2)
  ensures 
    valid_bit_string(res) && str2int(res) == str2int(s1) + str2int(s2)
{
  assume(false);
  unreached()
}

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (res: (Seq<char>, Seq<char>))
  requires 
    valid_bit_string(dividend) && valid_bit_string(divisor) && str2int(divisor) > 0
  ensures 
    valid_bit_string(res.0) && valid_bit_string(res.1) &&
    str2int(res.0) == str2int(dividend) / str2int(divisor) &&
    str2int(res.1) == str2int(dividend) % str2int(divisor)
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
fn mod_exp_pow2(sx: Vec<char>, sy: Vec<char>, n: u8, sz: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@) &&
    (str2int(sy@) == exp_int(2nat, n as nat) || str2int(sy@) == 0) &&
    sy@.len() == n as int + 1 &&
    str2int(sz@) > 1
  ensures 
    valid_bit_string(res@) &&
    str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@)
  decreases n
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 9): Fix ghost type usage by properly handling Seq to Vec conversion */
    if n == 0 {
        if sy.len() > 0 && sy[0] == '1' {
            let (_, r_seq) = div_mod(sx@, sz@);
            let mut res = Vec::new();
            let mut idx: usize = 0;
            let r_len = r_seq.len();
            while idx < r_len
                invariant
                    0 <= idx <= r_len,
                    r_len == r_seq.len(),
                    res@.len() == idx as nat,
                    forall|k: int| 0 <= k < idx ==> res@[k] == r_seq[k]
            {
                proof {
                    assert(idx < r_seq.len());
                }
                let ch = if r_seq[idx as int] == '1' { '1' } else { '0' };
                res.push(ch);
                idx = idx + 1;
            }
            proof {
                assert(res@ == r_seq);
            }
            return res;
        } else {
            let one = seq!['1'];
            let (_, r_seq) = div_mod(one, sz@);
            let mut res = Vec::new();
            let mut idx: usize = 0;
            let r_len = r_seq.len();
            while idx < r_len
                invariant
                    0 <= idx <= r_len,
                    r_len == r_seq.len(),
                    res@.len() == idx as nat,
                    forall|k: int| 0 <= k < idx ==> res@[k] == r_seq[k]
            {
                proof {
                    assert(idx < r_seq.len());
                }
                let ch = if r_seq[idx as int] == '1' { '1' } else { '0' };
                res.push(ch);
                idx = idx + 1;
            }
            proof {
                assert(res@ == r_seq);
            }
            return res;
        }
    } else {
        let mut half_y = Vec::new();
        let mut idx: usize = 1;
        let n_usize = n as usize;
        while idx <= n_usize
            invariant
                1 <= idx <= n_usize + 1,
                n_usize == n,
                half_y@.len() == idx - 1,
                forall|k: int| 0 <= k < idx - 1 ==> half_y@[k] == sy@[k + 1]
        {
            half_y.push(sy[idx]);
            idx = idx + 1;
        }
        let half_res = mod_exp_pow2(sx.clone(), half_y, (n - 1) as u8, sz.clone());
        let squared = add(half_res@, half_res@);
        let result = squared;
        
        if sy.len() > 0 && sy[0] == '1' {
            let (_, r_seq) = div_mod(result, sz@);
            let mut res = Vec::new();
            let mut idx2: usize = 0;
            let r_len = r_seq.len();
            while idx2 < r_len
                invariant
                    0 <= idx2 <= r_len,
                    r_len == r_seq.len(),
                    res@.len() == idx2 as nat,
                    forall|k: int| 0 <= k < idx2 ==> res@[k] == r_seq[k]
            {
                proof {
                    assert(idx2 < r_seq.len());
                }
                let ch = if r_seq[idx2 as int] == '1' { '1' } else { '0' };
                res.push(ch);
                idx2 = idx2 + 1;
            }
            proof {
                assert(res@ == r_seq);
            }
            return res;
        } else {
            let (_, r_seq) = div_mod(result, sz@);
            let mut res = Vec::new();
            let mut idx2: usize = 0;
            let r_len = r_seq.len();
            while idx2 < r_len
                invariant
                    0 <= idx2 <= r_len,
                    r_len == r_seq.len(),
                    res@.len() == idx2 as nat,
                    forall|k: int| 0 <= k < idx2 ==> res@[k] == r_seq[k]
            {
                proof {
                    assert(idx2 < r_seq.len());
                }
                let ch = if r_seq[idx2 as int] == '1' { '1' } else { '0' };
                res.push(ch);
                idx2 = idx2 + 1;
            }
            proof {
                assert(res@ == r_seq);
            }
            return res;
        }
    }
}
// </vc-code>


}

fn main() {}