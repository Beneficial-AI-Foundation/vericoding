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
    /* code modified by LLM (iteration 2): Fix syntax errors and implement complete circular shift logic for digits */
    let abs_x: int = if (x as int) < 0 { -(x as int) } else { x as int };
    let digits: Seq<char> = int_to_string(abs_x);
    let n: int = digits.len();
    let shift_int: int = shift as int;
    let raw_k = shift_int % n;
    let normalized_k: int = (raw_k + n) % n;
    let mut result_vec: Vec<char> = Vec::new();
    if shift_int > n {
        let rev: Seq<char> = reverse_string(digits);
        for i in 0..rev.len() {
            result_vec.push(rev[i]);
        }
    } else {
        if normalized_k == 0 {
            for i in 0..digits.len() {
                result_vec.push(digits[i]);
            }
        } else {
            let part1: Seq<char> = digits.subrange(n - normalized_k, n);
            let part2: Seq<char> = digits.subrange(0, n - normalized_k);
            let rotated: Seq<char> = part1.add(part2);
            for i in 0..rotated.len() {
                result_vec.push(rotated[i]);
            }
        }
    }
    result_vec
}
// </vc-code>


}

fn main() {}