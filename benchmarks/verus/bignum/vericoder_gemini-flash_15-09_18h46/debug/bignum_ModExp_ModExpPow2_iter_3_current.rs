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
/* helper modified by LLM (iteration 3): no change */
spec fn ModExp(x: nat, y: nat, z: nat) -> nat
  decreases y
{
  if y == 0 {
    1
  } else if y % 2 == 0 {
    let res = ModExp(x, y / 2, z);
    (res * res) % z
  } else {
    let res = ModExp(x, (y - 1) / 2, z);
    (x * res * res) % z
  }
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_ModExpPow2(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): changed `i` to `usize` for indexing and `bit_string_chars` to `Vec<char>` to avoid `ghost` type errors */
{
  let x_int = Str2Int(sx@);
  let y_int = Str2Int(sy@);
  let z_int = Str2Int(sz@);

  let res_int = ModExp(x_int, y_int, z_int);

  let mut temp_res: nat = res_int;
  let mut bit_string_chars: Vec<char> = Vec::new();

  if temp_res == 0 {
      bit_string_chars.push('0');
  } else {
      while temp_res > 0
          invariant
              temp_res >= 0,
              forall |i: int| 0 <= i && i < bit_string_chars.len() ==> (bit_string_chars@[i] == '0' || bit_string_chars@[i] == '1'),
          decreases temp_res
      {
          if temp_res % 2 == 1 {
              bit_string_chars.push('1');
          } else {
              bit_string_chars.push('0');
          }
          temp_res = temp_res / 2;
      }
  }

  let mut reversed_bit_string_chars: Vec<char> = Vec::new();
  let mut i: usize = if bit_string_chars.len() == 0 { 0 } else { bit_string_chars.len() - 1 };
  let mut _ghost_i: int = bit_string_chars.len() as int - 1;

  while (_ghost_i >= 0)
      invariant
          _ghost_i >= -1,
          _ghost_i < bit_string_chars.len() as int,
          reversed_bit_string_chars.len() == (bit_string_chars.len() as int - 1 - _ghost_i) as nat,
          forall |j: int| 0 <= j && j < reversed_bit_string_chars.len() ==> (reversed_bit_string_chars@[j] == '0' || reversed_bit_string_chars@[j] == '1'),
      decreases _ghost_i
  {
      reversed_bit_string_chars.push(bit_string_chars.index(i)@);
      if i > 0 {
          i = i - 1;
      }
      _ghost_i = _ghost_i - 1;
  }

  reversed_bit_string_chars
}
// </vc-code>

fn main() {}
}
