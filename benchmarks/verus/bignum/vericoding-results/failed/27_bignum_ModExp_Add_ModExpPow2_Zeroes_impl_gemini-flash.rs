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
/* helper modified by LLM (iteration 10): Corrected Seq::new() to take a type parameter and `add` calls to properly append a Seq<char>. Removed the loop in `int_to_bitstring_spec` as it's a spec function. Made type annotations `nat` explicit wherever needed. */
spec fn mul_mod_spec(a: nat, b: nat, m: nat) -> nat { (a * b) % m }
spec fn int_to_bitstring_spec(val: nat) -> (result: Seq<char>)
  ensures ValidBitString(result)
{
  if val == (0 as nat) { Seq::<char>::new().add('0') }
  else {
    let mut bit_seq = Seq::<char>::empty();
    let mut temp_val = val;
    // The loop logic for spec function needs `loop_invariant` and `decreases`, which is not allowed. We directly encode the recursive definition.
    // Since this is a spec function, Verus can reason about recursive definitions without explicit iteration.
    if temp_val > (0 as nat) {
      if (temp_val % (2 as nat)) == (1 as nat) {
        // Recursive case to prepend '1'
        bit_seq = int_to_bitstring_spec(temp_val / (2 as nat)).add('1');
      } else {
        // Recursive case to prepend '0'
        bit_seq = int_to_bitstring_spec(temp_val / (2 as nat)).add('0');
      }
    }
    bit_seq
  }
}
exec fn int_to_bitstring(val: nat) -> (res: Vec<char>)
  ensures ValidBitString(res@)
{
  let mut bit_vec = Vec::<char>::new();
  if val == (0 as nat) {
    bit_vec.push('0');
  }
  else {
    let mut temp: nat = val; // Explicit type annotation for clarity given the previous errors
    while temp > (0 as nat)
      invariant
        temp >= (0 as nat),
        forall |i: int| 0 <= i && i < bit_vec@.len() ==> (bit_vec@[i] == '0' || bit_vec@[i] == '1'),
      decreases temp
    {
      let rem: nat = temp % (2 as nat); // Explicit type annotation
      if rem == (1 as nat) { bit_vec.insert(0, '1'); }
      else { bit_vec.insert(0, '0'); }
      temp = temp / (2 as nat); // Explicit type annotation
    }
  }
  bit_vec
}

spec fn new_function_here_ModExp_Add_ModExpPow2_Zeroes_spec(sx: Seq<char>, sy_k: Seq<char>, sz: Seq<char>) -> (result: Seq<char>)
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
/* code modified by LLM (iteration 10): Fixed compiler errors related to `nat` and `int` mismatches by adding explicit type conversions and annotations. Also fixed the `Seq::new()` and `add()` calls according to the compiler help. */
{
    let x_int: nat = Str2Int(sx@);
    let y_int: nat = Str2Int(sy@);
    let z_int: nat = Str2Int(sz@);

    if y_int == (0 as nat) {
        return int_to_bitstring(1 as nat);
    } else {
        let k: nat = y_int / (2 as nat);
        let r: nat = y_int % (2 as nat);

        let sx_copy: Vec<char> = sx.to_vec();
        let sy_k_vec: Vec<char> = int_to_bitstring(k);
        let sz_copy: Vec<char> = sz.to_vec();

        let res_k = ModExp_Add_ModExpPow2_Zeroes(&sx_copy, &sy_k_vec, &sz_copy);

        let sq_res_k_int = mul_mod_spec(Str2Int(res_k@), Str2Int(res_k@), z_int);

        if r == (1 as nat) {
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
