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
/* helper modified by LLM (iteration 7): Removed all erroneous usage of Verus `int` type in `exec` function. */
spec fn mul_mod_spec(a: nat, b: nat, m: nat) -> nat { (a * b) % m }
spec fn int_to_bitstring_spec(val: nat) -> Seq<char>
  ensures ValidBitString(result)
{
  if val == 0 { Seq::new().add('0') }
  else {
    let mut bit_seq = Seq::<char>::empty();
    let mut temp_val = val;
    while temp_val > 0 {
      let rem = temp_val % 2; // rem is nat
      if rem == 1 { bit_seq = Seq::new().add('1').add(bit_seq); }
      else { bit_seq = Seq::new().add('0').add(bit_seq); }
      temp_val = temp_val / 2;
    }
    bit_seq
  }
}
exec fn int_to_bitstring(val: nat) -> (res: Vec<char>)
  ensures ValidBitString(res@)
{
  let mut bit_vec = Vec::<char>::new();
  if val == 0 {
    bit_vec.push('0');
  }
  else {
    let mut temp = val;
    while temp > 0
      invariant
        temp >= 0,
      decreases temp
    {
      let rem = temp % 2;
      if rem == 1 { bit_vec.insert(0, '1'); }
      else { bit_vec.insert(0, '0'); }
      temp = temp / 2;
    }
  }
  bit_vec
}

spec fn new_function_here_ModExp_Add_ModExpPow2_Zeroes_spec(sx: Seq<char>, sy_k: Seq<char>, sz: Seq<char>) -> Seq<char>
  requires
    ValidBitString(sx),
    ValidBitString(sy_k),
    ValidBitString(sz),
    sy_k.len() > 0,
    Str2Int(sz) > 1,
  ensures
    ValidBitString(result),
    Str2Int(result) == Exp_int(Str2Int(sx), Str2Int(sy_k)) % Str2Int(sz)
{
  int_to_bitstring_spec(Exp_int(Str2Int(sx), Str2Int(sy_k)) % Str2Int(sz))
}
// </vc-helpers>

// <vc-spec>
exec fn ModExp_Add_ModExpPow2_Zeroes(sx: &[char], sy: &[char], sz: &[char]) -> (res: Vec<char>)
  requires ValidBitString(sx@), ValidBitString(sy@), ValidBitString(sz@), sy@.len() > 0, Str2Int(sz@) > 1
  ensures ValidBitString(res@), Str2Int(res@) == Exp_int(Str2Int(sx@), Str2Int(sy@)) % Str2Int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 7): Changed type casting to `nat` instead of `int` for `if` conditions to resolve compilation errors. */
{
    let x_int: nat = Str2Int(sx@);
    let y_int: nat = Str2Int(sy@);
    let z_int: nat = Str2Int(sz@);

    if y_int == 0 {
        return int_to_bitstring(1);
    } else {
        let k: nat = y_int / 2;
        let r: nat = y_int % 2;

        let sx_copy: Vec<char> = sx.to_vec();
        let sy_k_vec: Vec<char> = int_to_bitstring(k);
        let sz_copy: Vec<char> = sz.to_vec();

        let res_k = ModExp_Add_ModExpPow2_Zeroes(&sx_copy, &sy_k_vec, &sz_copy);

        let sq_res_k_int = mul_mod_spec(Str2Int(res_k@), Str2Int(res_k@), z_int);

        if r == 1 {
            let final_res_int = mul_mod_spec(sq_res_k_int, x_int, z_int);
            return int_to_bitstring(final_res_int);
        } else {
            return int_to_bitstring(sq_res_k_int);
        }
    }
}
// </vc-code>

fn main() {}
}
