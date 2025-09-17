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
/* helper modified by LLM (iteration 3): fixed type mismatches in spec fn power2 by using nat literals for operations */
spec fn power2(exp: nat) -> nat
    decreases exp
{
  if exp == 0nat { 1nat } else { 2nat * power2(exp - 1nat) }
}

/* helper modified by LLM (iteration 3): fixed return variable and literals to nat type in exec fn str_to_nat */
exec fn str_to_nat(s: &[char]) -> nat
  requires ValidBitString(s@)
  ensures str_to_nat(s) == Str2Int(s@)
{
  let mut res = 0nat;
  let mut pow = 1nat;
  let mut i = s.len();
  while i > 0
      invariant
          0 <= i <= s.len(),
          pow == power2((s.len() - i) as nat),
          res == Str2Int(s@.subrange(i as int, s.len() as int)),
      decreases i
  {
    i = i - 1;
    if s[i] == '1' {
      res = res + pow;
    }
    pow = pow * 2nat;
  }
  return res;
}

/* helper modified by LLM (iteration 3): fixed type mismatches in nat_to_binary by using nat literals for division and modulo */
exec fn nat_to_binary(n: nat) -> Vec<char>
  ensures
      ValidBitString(nat_to_binary(n)@),
      Str2Int(nat_to_binary(n)@) == n
{
  if n == 0nat {
    let mut res = Vec::<char>::new();
    res.push('0');
    return res;
  } else {
    let mut res = nat_to_binary(n / 2nat);
    if n % 2nat == 0nat {
      res.push('0');
    } else {
      res.push('1');
    }
    return res;
  }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_DivMod_ModExpPow2_Zeroes(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 3): no changes needed, using helper functions to compute binary addition */
    let a_nat = str_to_nat(a);
    let b_nat = str_to_nat(b);
    let sum = a_nat + b_nat;
    return nat_to_binary(sum);
}
// </vc-code>

fn main() {}
}

