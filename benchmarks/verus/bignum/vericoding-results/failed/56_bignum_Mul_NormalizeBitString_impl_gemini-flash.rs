// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn str2int(s: Seq<char>) -> nat
  recommends valid_bit_string(s)
  decreases s.len()
{
  if s.len() == 0 { 
    0nat 
  } else { 
    2nat * str2int(s.subrange(0, s.len() - 1)) + (if s[s.len() - 1] == '1' { 1nat } else { 0nat })
  }
}

spec fn valid_bit_string(s: Seq<char>) -> bool {
  forall|i: int| 0 <= i < s.len() ==> (s[i] == '0' || s[i] == '1')
}

fn normalize_bit_string(s: Seq<char>) -> (t: Seq<char>)
  ensures 
    valid_bit_string(t),
    t.len() > 0,
    t.len() > 1 ==> t[0] != '0',
    valid_bit_string(s) ==> str2int(s) == str2int(t)
{
  assume(false);
  unreached()
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 10): Removed `nat_to_bit_string` as it was not actually required in the main `mul` function and could cause issues with `Seq` operations. */

// </vc-helpers>

// <vc-spec>
fn mul(s1: Vec<char>, s2: Vec<char>) -> (res: Vec<char>)
  requires 
    valid_bit_string(s1@) && valid_bit_string(s2@)
  ensures 
    valid_bit_string(res@),
    str2int(res@) == str2int(s1@) * str2int(s2@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 10): Replaced `temp_n as int` with `temp_n.value()` to perform arithmetic operations on `nat` types. This ensures `nat` values are handled correctly without unsafe casting, resolving compilation errors. */
{
    let n1 = str2int(s1@);
    let n2 = str2int(s2@);
    let product_nat: nat = n1 * n2;

    let mut result_vec = Vec::new();
    if product_nat == 0 {
        result_vec.push('0');
    } else {
        let mut temp_n: nat = product_nat;
        while temp_n > 0
            invariant
                temp_n >= 0,
                valid_bit_string(result_vec@.reverse()),
                str2int(result_vec@.reverse()) + (temp_n * (1nat << result_vec@.len())) == product_nat,
            decreases temp_n
        {
            let bit_char = if temp_n.value() % 2 == 1 { '1' } else { '0' };
            result_vec.insert(0, bit_char);
            temp_n = (temp_n.value() / 2) as nat;
        }
    }

    proof {
        assert(valid_bit_string(result_vec@));
        assert(str2int(result_vec@) == product_nat);
    }
    result_vec
}
// </vc-code>


}

fn main() {}