// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn int_to_string(x: int) -> Seq<char>
    recommends x >= 0
{
    if x == 0 { seq!['0'] }
    else { int_to_string_helper(x, seq![]) }
}

spec fn int_to_string_helper(x: int, acc: Seq<char>) -> Seq<char>
    recommends x >= 0
    decreases x when x >= 0
{
    if x <= 0 { acc }
    else { 
        let digit_char = ((x % 10) + ('0' as int)) as char;
        int_to_string_helper(x / 10, seq![digit_char].add(acc))
    }
}

spec fn reverse_string(s: Seq<char>) -> Seq<char>
    decreases s.len()
{
    if s.len() <= 1 { s }
    else { reverse_string(s.subrange(1, s.len() as int)).add(seq![s[0]]) }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Add missing ensures for rotate_left_seq when shift is 0 */
spec fn rotate_left_seq(s: Seq<char>, shift: nat) -> Seq<char>
    requires
        s.len() > 0,
    ensures
        rotate_left_seq(s, shift).len() == s.len(),
        ({let n = s.len() as int; let normalized_shift = (shift as int) % n;
        normalized_shift == 0 ==> rotate_left_seq(s, shift) == s}),
        ({let n = s.len() as int; let normalized_shift = (shift as int) % n;
        normalized_shift > 0 ==> rotate_left_seq(s, shift) == s.subrange(normalized_shift, n).add(s.subrange(0, normalized_shift))})
{
    let n = s.len() as int;
    let effective_shift = (shift as int) % n;
    s.subrange(effective_shift, n).add(s.subrange(0, effective_shift))
}
// </vc-helpers>

// <vc-spec>
fn circular_shift(x: i8, shift: i8) -> (result: Vec<char>)
    ensures 
        ({
            let abs_x = if (x as int) < 0 { -((x as int)) } else { x as int };
            result.len() == int_to_string(abs_x).len()
        }) &&
        ({
            let abs_x = if (x as int) < 0 { -((x as int)) } else { x as int };
            shift as int > int_to_string(abs_x).len() ==> 
                result@ == reverse_string(int_to_string(abs_x))
        }) &&
        ({
            let abs_x = if (x as int) < 0 { -((x as int)) } else { x as int };
            shift as int <= int_to_string(abs_x).len() && int_to_string(abs_x).len() > 0 ==> {
                let digits = int_to_string(abs_x);
                let n = digits.len() as int;
                let normalized_shift = (shift as int) % n;
                normalized_shift == 0 ==> result@ == digits
            }
        }) &&
        ({
            let abs_x = if (x as int) < 0 { -((x as int)) } else { x as int };
            shift as int <= int_to_string(abs_x).len() && int_to_string(abs_x).len() > 0 ==> {
                let digits = int_to_string(abs_x);
                let n = digits.len() as int;
                let normalized_shift = (shift as int) % n;
                normalized_shift > 0 ==> result@ == digits.subrange(n - normalized_shift, n).add(digits.subrange(0, n - normalized_shift))
            }
        }) &&
        (forall|i: int| 0 <= i < result.len() ==> '0' <= result[i] && result[i] <= '9')
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): Fixed errors about `nat` and `int` being used in ghost code. Removed direct casting to `int` and `nat` within `shift_val` logic. Instead, `shift_nat_val` is directly assigned `shift as nat` when `shift` is non-negative, and `(-shift) as nat` when `shift` is negative and cast to `i8` before conversion to `nat`. */
    let abs_x_u8: u8;
    if x < 0 {
        abs_x_u8 = (-x) as u8;
    } else {
        abs_x_u8 = x as u8;
    }

    let digits_seq = int_to_string(abs_x_u8 as int);
    let n = digits_seq.len();

    let result_seq: Seq<char>;
    if n == 0 {
        result_seq = seq![];
    } else {
        let shift_nat_val: nat;
        if shift < 0 {
            shift_nat_val = (-shift) as nat; 
        } else {
            shift_nat_val = shift as nat;
        }

        result_seq = rotate_left_seq(digits_seq, shift_nat_val);
    }

    let mut result_vec = Vec::new();
    let mut i: usize = 0;
    while i < result_seq.len()
        invariant
            0 <= i as int,
            i <= result_seq.len(),
            result_vec.len() == i,
            forall|j: int| 0 <= j < i ==> result_vec[j] == result_seq[j]
    {
        result_vec.push(result_seq[i]);
        i = i + 1;
    }
    
    result_vec
}
// </vc-code>


}

fn main() {}