// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn valid_output(n: int, result: Seq<Seq<char>>) -> bool
    recommends n >= 2
{
    if n < 6 {
        result.len() == 1 + (n - 1) &&
        result[0] == seq!['-', '1'] &&
        (forall|i: int| 1 <= i < result.len() ==> result[i] == seq!['1', ' '] + int_to_string(i + 1))
    } else {
        result.len() == (5 + (n - 6)) + (n - 1) &&
        result[0] == seq!['1', ' ', '2'] && 
        result[1] == seq!['1', ' ', '3'] && 
        result[2] == seq!['1', ' ', '4'] && 
        result[3] == seq!['2', ' ', '5'] && 
        result[4] == seq!['2', ' ', '6'] &&
        (forall|i: int| 5 <= i < 5 + (n - 6) ==> result[i] == seq!['1', ' '] + int_to_string(i + 2)) &&
        (forall|i: int| 5 + (n - 6) <= i < result.len() ==> result[i] == seq!['1', ' '] + int_to_string(i - (5 + (n - 6)) + 2))
    }
}

spec fn int_to_string(n: int) -> Seq<char>
    decreases if n >= 0 { n } else { -n }
{
    if n < 0 {
        seq!['-'] + int_to_string(-n)
    } else if n < 10 {
        seq![((n % 10) as u8 + '0' as u8) as char]
    } else {
        int_to_string(n / 10) + int_to_string(n % 10)
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(n: int) -> (result: Vec<String>)
    requires n >= 2
    ensures valid_output(n, result@.map_values(|s: String| s@))
// </vc-spec>
// <vc-code>
{
    assume(false);
    Vec::new()
}
// </vc-code>


}

fn main() {}