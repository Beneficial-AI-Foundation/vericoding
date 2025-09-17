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
spec fn nat_to_seq(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 {
        Seq::<char>::empty()
    } else {
        let r = nat_to_seq(n / 2);
        let bit = if n % 2 == 0 { '0' } else { '1' };
        r + Seq::new(1, |i| bit)
    }
}

proof fn nat_to_seq_correct(n: nat)
    ensures
        Str2Int(nat_to_seq(n)) == n,
    decreases n
{
    if n > 0 {
        nat_to_seq_correct(n / 2);
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_DivMod_ModExpPow2_Mul(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): Fixed compilation error by changing i to usize, res and cur to tracked nat, adjusted loop structure */
  let modd = Str2Int(sz@);
  let tracked mut res: nat = 1;
  let tracked mut cur: nat = Str2Int(sx@);
  let mut i: usize = sy.len() - 1;
  while i < sy.len()
    invariant
      i <= sy@.len(),
    decreases i
  {
    let bit = sy@[i];
    if bit == '1' {
      res = (res * cur) % modd;
    }
    cur = (cur * cur) % modd;
    if i == 0 {
      break;
    }
    i -= 1;
  }
  let result_nat = res;
  let result_seq = nat_to_seq(result_nat);
  let result_vec = Vec::from_seq(result_seq);
  return result_vec;
}
// </vc-code>

fn main() {}
}
