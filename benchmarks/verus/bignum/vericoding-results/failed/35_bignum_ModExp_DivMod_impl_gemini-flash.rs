// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn str2int(s: Seq<char>) -> nat
  recommends valid_bit_string(s)
  decreases s.len()
{
  if s.len() == 0 { 0nat } else { 2nat * str2int(s.subrange(0, (s.len() - 1) as int)) + (if s[(s.len() - 1) as int] == '1' { 1nat } else { 0nat }) }
}

spec fn exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

fn div_mod(dividend: Seq<char>, divisor: Seq<char>) -> (result: (Seq<char>, Seq<char>))
  requires 
      valid_bit_string(dividend) && valid_bit_string(divisor) &&
      str2int(divisor) > 0
  ensures 
      valid_bit_string(result.0) && valid_bit_string(result.1) &&
      str2int(result.0) == str2int(dividend) / str2int(divisor) &&
      str2int(result.1) == str2int(dividend) % str2int(divisor)
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Fixed type mismatch for `half_y` in mod_exp_auto_bits by making it an `int` for division, and added an `as nat` cast afterwards. */
spec fn mod_exp_auto_bits(x: nat, y: nat, z: nat) -> nat
    recommends
        y >= 0,
        z > 1
    ensures
        mod_exp_auto_bits(x, y, z) == exp_int(x, y) % z
    decreases y
{
    if y == 0 {
        1nat
    } else if y == 1 {
        x % z
    } else if y % 2 == 0 {
        let half_y: nat = (y / 2) as nat;
        let res = mod_exp_auto_bits(x, half_y, z);
        (res * res) % z
    } else {
        let half_y: nat = ((y - 1) / 2) as nat;
        let res_half = mod_exp_auto_bits(x, half_y, z);
        (x * (res_half * res_half)) % z
    }
}
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Vec<char>, sy: Vec<char>, sz: Vec<char>) -> (res: Vec<char>)
  requires 
      valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@) &&
      sy@.len() > 0 && str2int(sz@) > 1
  ensures 
      valid_bit_string(res@) &&
      str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@)
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Converted `result_int` to `int` for comparison with 0 and added a cast to `nat` when assigning to `temp_int_nat` to ensure proper type handling during the conversion to bit string. */
{
    let x_int = str2int(sx@);
    let y_int = str2int(sy@);
    let z_int = str2int(sz@);

    let result_int = mod_exp_auto_bits(x_int, y_int, z_int);

    // Convert result_int to its binary string representation
    let mut bit_string_result: Vec<char> = Vec::new();
    if (result_int as int) == 0 {
        bit_string_result.push('0');
    } else {
        let mut temp_int_nat: nat = result_int;
        while temp_int_nat > 0
            invariant
                temp_int_nat >= 0,
                valid_bit_string(bit_string_result@)
            decreases temp_int_nat
        {
            if temp_int_nat % 2 == 1 {
                bit_string_result.push('1');
            } else {
                bit_string_result.push('0');
            }
            temp_int_nat = temp_int_nat / 2;
        }
        bit_string_result.reverse();
    }
    bit_string_result
}
// </vc-code>


}

fn main() {}