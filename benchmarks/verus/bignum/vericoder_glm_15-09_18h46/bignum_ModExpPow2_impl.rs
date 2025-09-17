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
  let base = Str2Int(sx@);
  let exponent = Str2Int(sy@);
  let modulus = Str2Int(sz@);
  proof {
    if exponent == 0 {
      assert(Exp_int(base, 0) == 1);
      assert(1 % modulus == 1);
    } else {
      assert(exponent == Exp_int(2, n as nat));
    }
  }
  let mut result = 1;
  let mut current = base % modulus;
  let mut i = 0;
  while i < n
      invariant
          0 <= i && i <= n,
          result == Exp_int(base, Exp_int(2, i as nat)) % modulus,
          current == (Exp_int(base, Exp_int(2, i as nat)) % modulus),
          1 < modulus,
      decreases (n - i)
  {
    i = i + 1;
    current = (current * current) % modulus;
    proof {
      assert(Exp_int(2, i as nat) == Exp_int(2, (i - 1) as nat) * 2);
    }
  }
  result = current;
  let res_str = nat_to_bitstring(result);
  res_str
}

fn nat_to_bitstring(n: nat) -> Vec<char>
    ensures ValidBitString(result@),
        Str2Int(result@) == n
{
  if n == 0 {
    Vec::from(['0'])
  } else {
    let mut chars = Vec::<char>::new();
    let mut current = n;
    while current > 0
        invariant
            n >= 0,
            current >= 0,
            Str2Int(chars@) == n - current * Exp_int(2, chars.len()),
            Str2Int(chars@) >= 0,
            forall |i: int| 0 <= i && i < chars.len() as int ==> []["'"]["'0"], []["'"]["'1"].contains(chars@[i]),
        decreases current
    {
      let bit = if current % 2 == 1 { '1' } else { '0' };
      chars.push(bit);
      current = current / 2;
    }
    chars.reverse();
    if chars.is_empty() {
      chars.push('0');
    }
    chars
  }
}
// </vc-code>

fn main() {}
}


