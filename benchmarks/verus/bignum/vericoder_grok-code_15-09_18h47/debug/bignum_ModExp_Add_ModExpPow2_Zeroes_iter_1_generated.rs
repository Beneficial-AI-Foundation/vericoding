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
    if s.len() == 0 { 0 } else { 2 * Str2Int(s.subrange(0, s.len() as int - 1)) + (if s.index(s.len() as int - 1) == '1' { 1nat } else { 0nat }) }
}

spec fn ValidBitString(s: Seq<char>) -> bool
{
  forall |i: int| 0 <= i && i < s.len() as int ==> (s.index(i) == '0' || s.index(i) == '1')
}

// <vc-helpers>
spec fn Int2Str(n: nat) -> Seq<char>
  decreases n
  {
    if n == 0 { Seq::<char>::empty() } else { Int2Str(n / 2) + Seq::<char>::singleton(if n % 2 == 0 { '0' } else { '1' }) }
  }

proof fn lemma_int2str2int(n: nat)
  ensures
    Str2Int(Int2Str(n)) == n,
    ValidBitString(Int2Str(n))
  decreases n
{
  if n != 0 {
    lemma_int2str2int(n / 2);
  }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
  let m = Str2Int(sz@);
  let mut result: nat = 1;
  let mut base: nat = Str2Int(sx@);
  let mut exponent_bits = sy@;
  
  while exponent_bits.len() > 0
    invariant
      Str2Int(exponent_bits) <= Str2Int(sy@),
    decreases exponent_bits.len()
  {
    let last_index = exponent_bits.len() as nat - 1;
    let last_bit = exponent_bits.index(last_index);
    exponent_bits = exponent_bits.subrange(0, last_index as int);
    if last_bit == '1'
    {
      result = (result * base) % m;
    }
    base = (base * base) % m;
  }
  
  let result_seq = Int2Str(result);
  let mut res = Vec::<char>::new();
  let mut i: nat = 0;
  while i < result_seq.len()
    invariant
      true,
    decreases result_seq.len() as int - i as int
  {
    res.push(result_seq.index(i));
    i = i + 1;
  }
  res
}
// </vc-code>

fn main() {}
}
