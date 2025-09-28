// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int) -> bool {
    100 <= n <= 999
}

spec fn contains_seven(n: int) -> bool
    recommends valid_input(n)
{
    (n % 10) == 7 || ((n / 10) % 10) == 7 || (n / 100) == 7
}

spec fn valid_output(result: Seq<char>) -> bool {
    result == "Yes\n"@ || result == "No\n"@
}
// </vc-preamble>

// <vc-helpers>
fn contains_seven_impl(n: int) -> (result: bool)
    requires
        valid_input(n),
    ensures
        result == contains_seven(n),
{
    let units = n % 10;
    let tens = (n / 10) % 10;
    let hundreds = n / 100;
    units == 7 || tens == 7 || hundreds == 7
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: Vec<char>)
    requires valid_input(n as int)
    ensures 
        valid_output(result@) &&
        ((result@ == "Yes\n"@) <==> contains_seven(n as int))
// </vc-spec>
// <vc-code>
{
    let flag = contains_seven_impl(n as int);
    if flag {
        let mut result = Vec::new();
        result.push('Y');
        result.push('e');
        result.push('s');
        result.push('\n');
        result
    } else {
        let mut result = Vec::new();
        result.push('N');
        result.push('o');
        result.push('\n');
        result
    }
}
// </vc-code>


}

fn main() {}