
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
/* helper modified by LLM (iteration 3): No change as it was correct */
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
/* code modified by LLM (iteration 3): Fixed `nat`/`int` type issues by using `usize` for array indexing and ghost variables for Verus types. Also adjusted remainder normalization. */
{
    let mut q: Vec<char> = Vec::new();
    let mut r: Vec<char> = Vec::new();
    let n_usize: usize = dividend.len();
    let m_usize: usize = divisor.len();
    let n: int = dividend.len() as int;
    let m: int = divisor.len() as int;

    if n_usize == 0 {
        return (q, r);
    }

    let mut idx: usize = 0;
    while idx < n_usize
        invariant
            0 <= idx && idx <= n_usize,
            r.len() <= m_usize + 1,
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
            let ghost diff_int = temp_r_int - divisor_int;

            let mut new_r_vec: Vec<char> = Vec::new();
            let mut ghost temp_diff_ghost: nat = diff_int;
            if temp_diff_ghost == 0 {
                new_r_vec.push('0');
            } else {
                while temp_diff_ghost > 0
                    invariant
                        temp_diff_ghost.is_nat(),
                        ValidBitString(new_r_vec@),
                        // Proof that the accumulated bits and remaining `temp_diff_ghost` sum to `diff_int`
                        Str2Int(new_r_vec@) * pow2(new_r_vec.len() as nat) + temp_diff_ghost == diff_int,
                {
                    if (temp_diff_ghost % 2) == 1 {
                        new_r_vec.insert(0, '1');
                    } else {
                        new_r_vec.insert(0, '0');
                    }
                    temp_diff_ghost = temp_diff_ghost / 2;
                }
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


