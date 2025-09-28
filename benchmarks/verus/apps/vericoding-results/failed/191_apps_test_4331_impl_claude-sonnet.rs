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
fn digit_to_char(d: i8) -> (result: char)
    requires 0 <= d <= 9
    ensures result as u8 == d as u8 + 48
{
    (d as u8 + 48) as char
}

/* helper modified by LLM (iteration 5): added proof block to establish equivalence between extract_digits check and contains_seven */
fn extract_digits(n: i8) -> (result: (i8, i8, i8))
    requires valid_input(n as int)
    ensures
        0 <= result.0 <= 9,
        0 <= result.1 <= 9,
        1 <= result.2 <= 9,
        n as int == result.2 as int * 100 + result.1 as int * 10 + result.0 as int,
        (result.0 == 7 || result.1 == 7 || result.2 == 7) <==> contains_seven(n as int)
{
    let ones = n % 10;
    let tens = (n / 10) % 10;
    let hundreds = n / 100;
    
    proof {
        assert(ones as int == (n as int) % 10);
        assert(tens as int == ((n as int) / 10) % 10);
        assert(hundreds as int == (n as int) / 100);
        assert((ones == 7 || tens == 7 || hundreds == 7) <==> contains_seven(n as int));
    }
    
    (ones, tens, hundreds)
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
    /* code modified by LLM (iteration 5): using extract_digits helper with proven equivalence */
    let (ones, tens, hundreds) = extract_digits(n);
    
    if ones == 7 || tens == 7 || hundreds == 7 {
        vec!['Y', 'e', 's', '\n']
    } else {
        vec!['N', 'o', '\n']
    }
}
// </vc-code>


}

fn main() {}