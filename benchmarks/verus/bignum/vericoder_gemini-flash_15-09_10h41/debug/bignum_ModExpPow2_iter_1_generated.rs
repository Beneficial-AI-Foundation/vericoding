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
spec fn get_power(sy: Seq<char>) -> nat {
  if sy.index(0) == '1' { Exp_int(2, (sy.len() - 1) as nat) } else { 0 }
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
      let mut i = s.len() as int - 1;
      while i >= 0 
        invariant
          0 <= i + 1 && i + 1 <= s.len() as int,
          v.len() + i + 1 == s.len() as int,
          forall |j: int| 0 <= j && j < v.len() ==> v@[j] == s@[s.len() as int - 1 -j],
      {
        v.push(s@[i]);
        i = i - 1;
      }
      return v;
    }
  }

  let k = n as nat - 1;
  let sy_prime: Seq<char> = sy_seq.subrange(1, sy_seq.len() as int);
  let sy_prime_vec: Vec<char> = sy_prime.to_vec();

  let res_k = ModExpPow2(sx, sy_prime_vec.as_slice(), k as int, sz);
  let res_k_int = Str2Int(res_k@);

  let s_int_val = get_power(sy_seq);
  let mut final_int_val: nat = 0;

  if s_int_val == 0 {
    final_int_val = res_k_int % sz_int;
  } else if s_int_val == Exp_int(2, n as nat) {
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
  let mut i = s.len() as int - 1;
  while i >= 0 
    invariant
      0 <= i + 1 && i + 1 <= s.len() as int,
      v.len() + i + 1 == s.len() as int,
      forall |j: int| 0 <= j && j < v.len() ==> v@[j] == s@[s.len() as int - 1 -j],
  {
    v.push(s@[i]);
    i = i - 1;
  }
  return v;
}
// </vc-code>

fn main() {}
}


