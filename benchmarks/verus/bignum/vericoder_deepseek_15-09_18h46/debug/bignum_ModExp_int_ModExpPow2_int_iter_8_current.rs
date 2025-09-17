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
/* helper modified by LLM (iteration 8): Fixed nat literal syntax by removing invalid nat suffix */
spec fn power_mod(x: nat, y: nat, z: nat) -> nat
  requires z > 1
  decreases y
{
    if y == 0 {
        1
    } else {
        let half = power_mod(x, (y - 1) as nat, z);
        (x * half) % z
    }
}

proof fn power_mod_lemma(x: nat, y: nat, z: nat)
  requires z > 1
  ensures power_mod(x, y, z) == Exp_int(x, y) % z
  decreases y
{
    if y > 0 {
        power_mod_lemma(x, (y - 1) as nat, z);
    }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_int_ModExpPow2_int(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 8): Fixed nat literal syntax by removing invalid nat suffix and using proper integer operations */
{
  proof {
    power_mod_lemma(Str2Int(sx@), Str2Int(sy@), Str2Int(sz@));
  }
  
  let x_int = Str2Int(sx@);
  let y_int = Str2Int(sy@);
  let z_int = Str2Int(sz@);
  let result_int = power_mod(x_int, y_int, z_int);
  
  let mut res: Vec<char> = Vec::new();
  let mut n: nat = result_int;
  
  if n == 0 {
      res.push('0');
  } else {
      while n > 0
          invariant
              ValidBitString(res@),
              Str2Int(res@) == n,
          decreases n
      {
          if n % 2 == 0 {
              res.push('0');
          } else {
              res.push('1');
          }
          n = n / 2;
      }
      res.reverse();
  }
  
  res
}
// </vc-code>

fn main() {}
}
