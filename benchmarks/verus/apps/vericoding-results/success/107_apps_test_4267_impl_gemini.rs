// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_temperature(temp: int) -> bool {
    -40 <= temp <= 40
}

spec fn expected_output(temp: int) -> Seq<char> {
    if temp >= 30 { seq!['Y', 'e', 's', '\n'] } else { seq!['N', 'o', '\n'] }
}

spec fn correct_output(temp: int, output: Seq<char>) -> bool {
    output == expected_output(temp)
}
// </vc-preamble>

// <vc-helpers>
fn get_yes_vec() -> (result: Vec<u8>)
    ensures
        result@.map(|i: int, b: u8| b as char) == seq!['Y', 'e', 's', '\n'],
{
    vec!['Y' as u8, 'e' as u8, 's' as u8, '\n' as u8]
}

fn get_no_vec() -> (result: Vec<u8>)
    ensures
        result@.map(|i: int, b: u8| b as char) == seq!['N', 'o', '\n'],
{
    vec!['N' as u8, 'o' as u8, '\n' as u8]
}
// </vc-helpers>

// <vc-spec>
fn solve(x: i8) -> (result: Vec<u8>)
    requires valid_temperature(x as int)
    ensures correct_output(x as int, result@.map(|i: int, b: u8| b as char))
// </vc-spec>
// <vc-code>
{
    if x >= 30 {
        get_yes_vec()
    } else {
        get_no_vec()
    }
}
// </vc-code>


}

fn main() {}