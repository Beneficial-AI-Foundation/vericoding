// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(r: int) -> bool {
    1 <= r <= 100
}

spec fn dodecagon_area(r: int) -> int {
    3 * r * r
}

spec fn int_to_string(n: int) -> Seq<char>
    decreases n
{
    if n == 0 {
        seq!['0']
    } else if n < 10 {
        seq![('0' as int + n) as char]
    } else {
        int_to_string(n / 10) + int_to_string(n % 10)
    }
}

spec fn string_to_int(s: Seq<char>) -> int
    decreases s.len()
{
    if s.len() == 1 {
        (s[0] as int) - ('0' as int)
    } else if s.len() > 1 {
        string_to_int(s.subrange(0, s.len() - 1)) * 10 + ((s[s.len() - 1] as int) - ('0' as int))
    } else {
        0
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): remove use of unwrap. */
spec fn parse_input_and_calculate_area(input: &str) -> (area_value: Result<int, Seq<char>>) {
    let s = input.trim();
    let mut chars: Seq<char> = Seq::new(s.len() as nat, |i: nat| input.chars().nth(i as usize).unwrap());

    if s.len() == 0 {
        Result::Err(seq!['I', 'n', 'v', 'a', 'l', 'i', 'd', ' ', 'i', 'n', 'p', 'u', 't', ':', ' ', 'E', 'm', 'p', 't', 'y', ' ', 's', 't', 'r', 'i', 'n', 'g'])
    } else {
        let r_val = string_to_int(chars);
        if valid_input(r_val) {
            Result::Ok(dodecagon_area(r_val))
        } else {
            Result::Err(int_to_string(r_val) + seq![' ', 'i', 's', ' ', 'o', 'u', 't', ' ', 'o', 'f', ' ', 'r', 'a', 'n', 'g', 'e', ' ', '(', '1', '-', '1', '0', '0', ')'])
        }
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(stdin_input: &str) -> (output: String)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Changed `nat` to `usize` for loop indices. */
{
    let result = parse_input_and_calculate_area(stdin_input);
    match result {
        Result::Ok(area) => {
            let area_str = int_to_string(area);
            let mut final_string: String = String::new();
            let mut i: usize = 0;
            while (i as nat) < area_str.len()
                invariant
                    (final_string.len() as nat) == i as nat,
                    (i as nat) <= area_str.len(),
            {
                final_string.push(area_str@[i as nat]);
                i = i + 1;
            }
            final_string
        },
        Result::Err(err_msg) => {
            let mut final_string: String = String::new();
            let mut i: usize = 0;
            while (i as nat) < err_msg.len()
                invariant
                    (final_string.len() as nat) == i as nat,
                    (i as nat) <= err_msg.len(),
            {
                final_string.push(err_msg@[i as nat]);
                i = i + 1;
            }
            final_string
        },
    }
}
// </vc-code>


}

fn main() {}