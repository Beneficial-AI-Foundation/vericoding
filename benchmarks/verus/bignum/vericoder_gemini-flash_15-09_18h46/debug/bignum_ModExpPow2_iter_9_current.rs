use vstd::prelude::*;

verus! {

spec fn Exp_int(x: nat, y: nat) -> nat
    decreases y 
  {
    if y == 0 { 1 } else { x * Exp_int(x, (y - 1) as nat) }
  }
  
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
  // All characters must be '0' or '1'.
  forall |i: int| 0 <= i && i < s.len() as int ==>
    (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
exec fn ModExpPow2(sx: &[char], sy: &[char], n: int, sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@),
    n >= 0,
    (Str2Int(sy@) == Exp_int(2, n as nat) || Str2Int(sy@) == 0),
    sy@.len() == (n as nat) + 1,
    Str2Int(sz@) > 1
  ensures ValidBitString(res@),
    Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases n
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 9): Fixed `nat` suffix errors and type mismatches (`int` vs `usize`) in array indexing. Specifically, fixed `n == 0` check and index type casting. Changed `temp_val == 0nat` to `temp_val == 0` for `nat` comparison, and `temp_val % 2nat` and `temp_val / 2nat` expressions to `temp_val % 2` and `temp_val / 2`, also for `nat` values. */
{
    let x_int = Str2Int(sx@);
    let y_int = Str2Int(sy@);
    let z_int = Str2Int(sz@);

    if n == 0 as int {

        let mut vec_res = Vec::<char>::new();
        if x_int % z_int == 1 {
            vec_res.push('1');
        } else {
            vec_res.push('0');
        }
        vec_res
    } else {
        let current_bit = sy[n as usize];

        let mut sy_prime_vec = Vec::<char>::new();

        let mut i: int = 0;
        while i < n
        invariant
            0 <= i,
            i <= n,
            sy_prime_vec.len() == i as nat,
            forall |j: int| 0 <= j && j < i ==> sy_prime_vec@[j] == sy[j as usize],
        decreases (n - i)
        {
            sy_prime_vec.push(sy[i as usize]);
            i = i + 1;
        }
        let sy_prime = sy_prime_vec@;

        let res_prime_vec = ModExpPow2(sx, sy_prime_vec.as_slice(), n - 1, sz);
        let res_prime = Str2Int(res_prime_vec@);

        let mut res_vec = Vec::<char>::new();

        let final_int = if current_bit == '0' {
            res_prime
        } else {
            (res_prime * (x_int % z_int)) % z_int
        };
        
        let mut temp_val = final_int;
        if temp_val == 0 && n == 0 {
            res_vec.push('0');
        } else if temp_val == 0 {
            res_vec.push('0');
        } else {
            while temp_val > 0
                invariant
                    temp_val >= 0,
                    forall |idx: int| 0 <= idx && idx < res_vec.len() ==> (res_vec@[idx] == '0' || res_vec@[idx] == '1'),
                decreases temp_val
            {
                if temp_val % 2 == 1 {
                    res_vec.insert(0, '1');
                } else {
                    res_vec.insert(0, '0');
                }
                temp_val = temp_val / 2;
            }
        }

        res_vec
    }
}
// </vc-code>

fn main() {}
}


