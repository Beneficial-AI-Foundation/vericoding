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

spec fn valid_bit_string(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}
// </vc-preamble>

// <vc-helpers>
spec fn reversed_seq(s: Seq<char>) -> Seq<char> {
    s.reverse()
}

/* helper modified by LLM (iteration 9): add decreases clause to while loop */
fn reverse_vec(v: Vec<char>) -> (res: Vec<char>)
    ensures
        res@ == reversed_seq(v@)
{
    let n = v.len();
    let mut res = Vec::with_capacity(n);
    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            res@ == reversed_seq(v@.subrange((n - i) as int, n as int))
        decreases n - i
    {
        res.push(v[n - 1 - i]);
        i += 1;
    }
    res
}

/* helper modified by LLM (iteration 9): add decreases clause to while loop */
fn create_filled_vec(len: usize, fill_char: char) -> (res: Vec<char>)
    ensures
        res.len() == len,
        forall|i: int| 0 <= i < len ==> res[i] == fill_char
{
    let mut res = Vec::with_capacity(len);
    let mut i = 0;
    while i < len
        invariant
            0 <= i <= len,
            res.len() == i,
            forall|j: int| 0 <= j < i ==> res[j] == fill_char
        decreases len - i
    {
        res.push(fill_char);
        i += 1;
    }
    res
}
// </vc-helpers>

// <vc-spec>
fn mul(s1: Vec<char>, s2: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(s1@) && valid_bit_string(s2@)
  ensures 
    valid_bit_string(res@) &&
    str2int(res@) == str2int(s1@) * str2int(s2@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 10): fix decreases clause syntax */
    let rev_s1 = reverse_vec(s1);
    let rev_s2 = reverse_vec(s2);
    let n = rev_s1.len();
    let m = rev_s2.len();
    let total_len = n + m;
    let mut res_rev = create_filled_vec(total_len, '0');

    for i in 0..m {
        if rev_s2[i] == '1' {
            let mut carry = 0i32;
            for j in 0..n {
                let idx = i + j;
                let current_val = if res_rev[idx] == '1' { 1i32 } else { 0i32 };
                let s1_val = if rev_s1[j] == '1' { 1i32 } else { 0i32 };
                let total = current_val + s1_val + carry;
                carry = total / 2i32;
                res_rev[idx] = if (total % 2i32) == 1 { '1' } else { '0' };
            }
            let mut k = i + n;
            while carry > 0 && k < total_len
                decreases carry, total_len - k
            {
                let current_val = if res_rev[k] == '1' { 1i32 } else { 0i32 };
                let total = current_val + carry;
                carry = total / 2i32;
                res_rev[k] = if (total % 2i32) == 1 { '1' } else { '0' };
                k += 1;
            }
        }
    }

    let res = reverse_vec(res_rev);
    res
}
// </vc-code>


}

fn main() {}