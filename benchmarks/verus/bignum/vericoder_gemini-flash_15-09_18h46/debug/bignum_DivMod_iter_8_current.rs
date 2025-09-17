
use vstd::prelude::*;

verus! {

spec fn Str2Int(s: Seq<char>) -> nat
  recommends ValidBitString(s)
  decreases s.len()
{
  if s.len() == 0 {
    0
  } else {
    2 * Str2Int(s.subrange(0, s.len() as int - 1))
      + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat })
  }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
/* helper modified by LLM (iteration 8): No change */
spec fn lt_seq_char(s1: Seq<char>, s2: Seq<char>) -> bool {
    Str2Int(s1) < Str2Int(s2)
}
// </vc-helpers>

// <vc-spec>
exec fn DivMod(dividend: &[char], divisor: &[char]) -> (res: (Vec<char>, Vec<char>))
  requires ValidBitString(dividend@), ValidBitString(divisor@), Str2Int(divisor@) > 0
  ensures ValidBitString(res.0@) && ValidBitString(res.1@),
    Str2Int(res.0@) == Str2Int(dividend@) / Str2Int(divisor@),
    Str2Int(res.1@) == Str2Int(dividend@) % Str2Int(divisor@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 8): Type mismatches for `temp_diff_ghost` fixed by explicitly casting to nat where needed */
{
    let mut q: Vec<char> = Vec::new();
    let mut r: Vec<char> = Vec::new();
    let n: usize = dividend.len();
    let m: usize = divisor.len();

    if n == 0 {
        return (q, r);
    }

    let mut idx: usize = 0;
    while idx < n
        invariant
            0 <= idx && idx <= n,
            r.len() <= m + 1,
            ValidBitString(r@),
            q.len() == idx,
            ValidBitString(q@),
    {
        r.push(dividend[idx]);
        proof {
            assert(ValidBitString(r@));
        }

        if Str2Int(r@) < Str2Int(divisor@) {
            q.push('0');
        } else {
            q.push('1');
            let ghost temp_r_int = Str2Int(r@);
            let ghost divisor_int = Str2Int(divisor@);
            let ghost diff_int = (temp_r_int - divisor_int) as nat;

            let mut new_r_vec: Vec<char> = Vec::new();
            let ghost mut temp_diff_ghost: nat = diff_int;

            if temp_diff_ghost == 0 {
                new_r_vec.push('0');
            } else {
                while temp_diff_ghost > 0
                    invariant
                        temp_diff_ghost >= 0,
                        ValidBitString(new_r_vec@),
                        forall|j: int| 0 <= j && j < new_r_vec.len() ==> (new_r_vec@.index(j) == '0' || new_r_vec@.index(j) == '1'),
                {
                    if (temp_diff_ghost % 2) == 1 {
                        new_r_vec.push('1');
                    } else {
                        new_r_vec.push('0');
                    }
                    temp_diff_ghost = (temp_diff_ghost / 2) as nat;
                }
                new_r_vec.reverse();
            }
            r = new_r_vec;
        }

        idx = idx + 1;
    }

    // Normalize remainder to remove leading zeros, but keep '0' for value 0.
    let mut final_r: Vec<char> = Vec::new();
    let mut found_one = false;
    if r.len() == 0 {
        final_r.push('0');
    } else {
        for i in 0..r.len() {
            if r[i] == '1' {
                found_one = true;
            }
            if found_one {
                final_r.push(r[i]);
            }
        }
        if !found_one {
            final_r.push('0');
        }
    }
    r = final_r;

    (q, r)
}
// </vc-code>

fn main() {}
}


