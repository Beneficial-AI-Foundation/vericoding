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
/* helper modified by LLM (iteration 5): Removed char type. This helper is still unnecessary as its functionality is a basic check for '0' or '1' which can be performed directly */
spec fn get_power_val(s_idx_0: char) -> bool {
    s_idx_0 == '1'
}
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
/* code modified by LLM (iteration 5): Fixed type errors related to `int` and `nat` within `exec` functions by casting to `usize` for array indexing and using `nat` for `Str2Int` return values. The problematic `sy_seq.len() as int` was also updated to `sy_seq.len()` as the `.len()` method already returns an `int` for `Seq<char>` */
{
  let sx_int = Str2Int(sx@);
  let sz_int = Str2Int(sz@);
  let sy_seq = sy@;

  if n == 0 {
    assert(sy_seq.len() == 1);
    assert(sy_seq.index(0) == '0' || sy_seq.index(0) == '1');

    if Str2Int(sy_seq) == 0 && !sz_int.is_zero() {
      let mut v = Vec::<char>::new();
      v.push('1');
      return v;
    } else {
      // For sy = 1 (2^0), the calculation is (sx % sz)
      let rem = sx_int % sz_int;
      let mut s = Seq::<char>::new();
      let mut temp_rem = rem;
      if temp_rem == 0 {
        s = s.push('0');
      } else {
        while temp_rem > 0 {
          if temp_rem % 2 == 1 {
            s = s.push('1');
          } else {
            s = s.push('0');
          }
          temp_rem = temp_rem / 2;
        }
      }
      let mut v = Vec::<char>::new();
      let mut i: usize = s.len() as usize; // Change: Start i from s.len() - 1, loop till 0
      while i > 0 
        invariant
          0 <= (i as int) && (i as int) <= s.len() as int,
          v.len() + (i as int) == s.len() as int,
          forall |j: int| 0 <= j && j < v.len() ==> v@[j] == s@[s.len() as int - 1 - j],
      {
        i = i - 1; // Change: Decrement i at the start of loop for correct indexing
        v.push(s@[i as int]);
      }
      
      // Special handling for i=0 if loop condition above changes to `i > 0`
      if s.len() > 0 && v.len() == 0 {
        v.push(s@[0]);
      }
      return v;
    }
  }

  let k: int = n - 1;
  let sy_prime: Seq<char> = sy_seq.subrange(1, sy_seq.len());
  let sy_prime_vec: Vec<char> = sy_prime.to_vec();

  let res_k = ModExpPow2(sx, sy_prime_vec.as_slice(), k, sz);
  let res_k_int = Str2Int(res_k@);

  let s_char_is_one = get_power_val(sy_seq.index(0));
  let mut final_int_val: nat = 0;

  if !s_char_is_one {
    final_int_val = res_k_int % sz_int;
  } else {
    final_int_val = (res_k_int * res_k_int) % sz_int;
  }

  let mut s = Seq::<char>::new();
  let mut temp_final_int = final_int_val;
  if temp_final_int == 0 {
    s = s.push('0');
  } else {
    while temp_final_int > 0 
      invariant
        final_int_val == (temp_final_int * Exp_int(2, s.len() as nat)) + Str2Int(s.reverse()),
    {
      if temp_final_int % 2 == 1 {
        s = s.push('1');
      } else {
        s = s.push('0');
      }
      temp_final_int = temp_final_int / 2;
    }
  }
  
  let mut v = Vec::<char>::new();
  let mut i: usize = s.len() as usize; // Change: Start i from s.len() - 1, loop till 0

  while i > 0 
    invariant
      0 <= (i as int) && (i as int) <= s.len() as int,
      v.len() + (i as int) == s.len() as int,
      forall |j: int| 0 <= j && j < v.len() ==> v@[j] == s@[s.len() as int - 1 - j],
  {
    i = i - 1; // Change: Decrement i at the start of loop for correct indexing
    v.push(s@[i as int]);
  }
  
  // Special handling for i=0 if loop condition above changes to `i > 0`
  if s.len() > 0 && v.len() == 0 {
    v.push(s@[0]);
  }
  return v;
}
// </vc-code>

fn main() {}
}


