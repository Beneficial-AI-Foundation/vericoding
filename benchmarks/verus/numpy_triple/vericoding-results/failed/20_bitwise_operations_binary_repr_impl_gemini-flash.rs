// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn nat_to_binary_string(n: nat) -> Seq<char>
    decreases n
{
    if n == 0 {
        seq!['0']
    } else {
        let digit = if n % 2 == 0 { '0' } else { '1' };
        nat_to_binary_string(n / 2).push(digit)
    }
}

spec fn is_valid_binary(s: Seq<char>) -> bool {
    s.len() > 0 && (forall|i: int| 0 <= i < s.len() ==> s[i] == '0' || s[i] == '1')
}

spec fn is_valid_signed_binary(s: Seq<char>) -> bool {
    if s.len() > 0 && s[0] == '-' {
        is_valid_binary(s.skip(1))
    } else {
        is_valid_binary(s)
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Corrected `to_binary_unsigned_padded` logic to build from most significant bit to least significant. */
spec fn to_binary_unsigned_padded(n: nat, width: nat) -> Seq<char>
    requires width >= 1
    decreases width
{
    if width == 1 {
        if n % 2 == 0 { seq!['0'] } else { seq!['1'] }
    } else {
        let msb = (n >> (width - 1)) % 2;
        let digit = if msb == 0 { '0' } else { '1' };
        seq![digit] + to_binary_unsigned_padded(n, width - 1)
    }
}
// </vc-helpers>

// <vc-spec>
fn binary_repr(num: i32, width: Option<usize>) -> (result: Vec<char>)
    requires 
        width.is_some() ==> width.get_Some_0() >= 1,
    ensures 

        width.is_none() ==> is_valid_signed_binary(result@),
        width.is_some() ==> is_valid_binary(result@),

        width.is_some() ==> result.len() == width.get_Some_0(),

        (num >= 0 && width.is_none()) ==> 
            result@ == nat_to_binary_string(num as nat),

        (num < 0 && width.is_none()) ==> 
            result@.len() > 0 && result@[0] == '-' && is_valid_binary(result@.skip(1)),

        (num < 0 && width.is_some()) ==> {
            let w = width.get_Some_0();
            let two_comp = (1u32 << w) as i32 + num;
            two_comp >= 0 && two_comp < (1i32 << w) && result.len() == w
        }
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed compilation error by changing `width.get_Some_0()` to `width.get_Some_0() as int` only when used in ghost code. */
{
        let mut result_vec: Vec<char> = Vec::new();

        if num >= 0 {
            let ghost n_nat = num as nat;
            if width.is_some() {
                let w = width.get_Some_0(); // Keep usize for concrete use
                let ghost uw = w as nat; // For ghost reasoning
                if w == 0 {
                    // result_vec stays empty
                } else {
                    let ghost temp = to_binary_unsigned_padded(n_nat, uw);
                    result_vec = temp.to_vec();
                }
            } else {
                let ghost temp = nat_to_binary_string(n_nat);
                result_vec = temp.to_vec();
            }
        } else {
            if width.is_some() {
                let w = width.get_Some_0(); // Keep usize for concrete use
                let ghost uw = w as nat; // For ghost reasoning

                if uw == 0 {
                    // result_vec stays empty
                } else {
                    let two_comp_val = (1u64 << uw) as i32 + num;
                    let ghost n_nat = two_comp_val as nat;
                    let ghost temp = to_binary_unsigned_padded(n_nat, uw);
                    result_vec = temp.to_vec();
                }
            } else {
                result_vec.push('-');

                let positive_num = -num;
                let ghost n_nat = positive_num as nat;
                
                let ghost temp = nat_to_binary_string(n_nat);
                result_vec.extend_from_slice(temp.as_slice());
            }
        }

        result_vec
    }
// </vc-code>

}
fn main() {}