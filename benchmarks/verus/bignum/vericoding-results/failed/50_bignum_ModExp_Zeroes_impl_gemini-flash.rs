// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn str2int(s: Seq<char>) -> nat
  decreases s.len()
{
  if s.len() == 0 { 0nat } else { 2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat }) }
}

spec fn exp_int(x: nat, y: nat) -> nat
  decreases y
{
  if y == 0 { 1nat } else { x * exp_int(x, (y - 1) as nat) }
}

spec fn valid_bit_string(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1'
}

spec fn all_zero(s: Seq<char>) -> bool
{
  forall|i: int| 0 <= i < s.len() ==> s[i] == '0'
}

fn zeros(n: nat) -> (s: Seq<char>)
  ensures
    s.len() == n,
    valid_bit_string(s),
    str2int(s) == 0,
    all_zero(s),
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Corrected type and resolution errors. Changed `vstd::string::StrIng` to `vstd::string::String` and ensured `i` is of type `usize` for indexing. Also, cast `len()` to `usize` for array access. */
fn str2int_to_bit_string(n: u64) -> (s: Vec<char>)
  ensures
    valid_bit_string(s@),
    str2int(s@) == n as nat,
{
  if n == 0 {
    vec!['0']
  } else {
    let mut result_vec = vstd::string::String::new();
    let mut temp_n: u64 = n;
    while temp_n > 0
      invariant
        temp_n >= 0,
        result_vec@.len() as int >= 0,
        valid_bit_string(result_vec@),
        (temp_n as nat * exp_int(2 as nat, result_vec@.len() as nat)) + str2int(result_vec@) == n as nat
      decreases temp_n
    {
      if temp_n % 2 == 1 {
        result_vec.push('1');
      } else {
        result_vec.push('0');
      }
      temp_n = temp_n / 2;
    }
    let mut final_result: Vec<char> = Vec::new();
    let mut i: usize = result_vec@.len() - 1;
    while (i as int) >= 0
      invariant
        (i as int) >= -1,
        i < result_vec@.len(),
        final_result.len() == result_vec@.len() - 1 - i,
        forall|j: int| 0 <= j < final_result.len() ==> final_result[j] == result_vec@[result_vec@.len() - 1 - j as usize]
      decreases i
    {
      final_result.push(result_vec@[i]);
      if i == 0 { break; }
      i = i - 1;
    }
    final_result
  }
}
// </vc-helpers>

// <vc-spec>
fn mod_exp(sx: Vec<char>, sy: Vec<char>, sz: Vec<char>) -> (res: Vec<char>)
  requires
    valid_bit_string(sx@) && valid_bit_string(sy@) && valid_bit_string(sz@),
    sy@.len() > 0 && str2int(sz@) > 1,
  ensures
    valid_bit_string(res@),
    str2int(res@) == exp_int(str2int(sx@), str2int(sy@)) % str2int(sz@),
  decreases sy@.len()
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Fixed recursion. The recursion base case for `y == 1` was incorrect and should recurse with `y-1`. The `str2int_to_bit_string` helper was also used directly. */
{
  let x = str2int(sx@);
  let y: nat = str2int(sy@);
  let z = str2int(sz@);

  if y == 0 {
    vec!['1']
  } else {
    let y_minus_1_u64: u64 = (y - 1) as u64;
    let y_minus_1_str_vec = str2int_to_bit_string(y_minus_1_u64);
    let result_rec_vec = mod_exp(sx.clone(), y_minus_1_str_vec, sz.clone());
    let result_rec = str2int(result_rec_vec@);

    let current_res = (result_rec * x) % z;
    
    let final_res_vec = str2int_to_bit_string(current_res as u64);
    final_res_vec
  }
}
// </vc-code>


}

fn main() {}