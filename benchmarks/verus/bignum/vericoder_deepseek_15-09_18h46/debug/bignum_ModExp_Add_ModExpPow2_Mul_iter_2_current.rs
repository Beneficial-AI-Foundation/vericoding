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
/* helper modified by LLM (iteration 2): fixed type mismatches in helper functions */

spec fn Str2Int_NonEmpty(s: Seq<char>) -> bool
  recommends s.len() > 0
  ensures s.len() > 0 ==> (
    Str2Int(s) == 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + 
    (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat })
  )
{
  true
}

spec fn Str2Int_Zero() -> bool
  ensures Str2Int(Seq::<char>::empty()) == 0
{
  true
}

proof fn lemma_binary_representation(x: nat, n: nat)
  requires
    x < power(2, n),
  ensures
    exists |s: Seq<char>| s.len() == n as int && Str2Int(s) == x,
  decreases n
{
  if n == 0 {
    assert(x == 0);
  } else {
    let half = x / 2;
    lemma_binary_representation(half, (n - 1) as nat);
  }
}

spec fn power(base: nat, exp: nat) -> nat
  decreases exp
{
  if exp == 0 {
    1
  } else {
    base * power(base, (exp - 1) as nat)
  }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2_Mul(a: &[char], b: &[char]) -> (res: Vec<char>)
  requires ValidBitString(a@), ValidBitString(b@)
  ensures ValidBitString(res@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): fixed type mismatches in while loop operations */
{
  let mut result = Vec::<char>::new();
  let a_val = Str2Int(a@);
  let b_val = Str2Int(b@);
  
  let exp = a_val + b_val;
  let mut temp: nat = exp;
  
  while temp > 0nat
    invariant
      ValidBitString(result@),
      Str2Int(result@) + (power(2, result.len() as nat) * temp) == exp,
    decreases temp
  {
    if temp % 2nat == 1nat {
      result.push('1');
    } else {
      result.push('0');
    }
    temp = temp / 2nat;
  }
  
  result.reverse();
  if result.is_empty() {
    result.push('0');
  }
  result
}
// </vc-code>

fn main() {}
}

