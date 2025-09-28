// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(n: int) -> bool {
    1000 <= n <= 9999
}

spec fn extract_digits(n: int) -> (int, int, int, int) {
    let d1 = n / 1000;
    let d2 = (n / 100) % 10;
    let d3 = (n / 10) % 10;
    let d4 = n % 10;
    (d1, d2, d3, d4)
}

spec fn is_good(n: int) -> bool {
    let (d1, d2, d3, d4) = extract_digits(n);
    (d1 == d2 && d2 == d3) || (d2 == d3 && d3 == d4)
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_extract_digits_properties(n: int)
    requires
        valid_input(n),
    ensures
        ({
        let (d1, d2, d3, d4) = extract_digits(n);
        n == d1 * 1000 + d2 * 100 + d3 * 10 + d4
        && 1 <= d1 <= 9
        && 0 <= d2 <= 9
        && 0 <= d3 <= 9
        && 0 <= d4 <= 9
        })
{
    /* helper modified by LLM (iteration 4): Simplified proof without decreases clause */
    reveal(extract_digits);
    assert(n / 1000 <= 9) by {
        assert(n <= 9999);
    };
    assert(n / 1000 >= 1) by {
        assert(n >= 1000);
    };
}
// </vc-helpers>

// <vc-spec>
fn solve(n: i8) -> (result: bool)
    requires 
        valid_input(n as int),
    ensures 
        result <==> is_good(n as int),
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): Removed illegal ghost code from executable function */
    let num = n as i32;
    let d1 = (num / 1000) % 10;
    let d2 = (num / 100) % 10;
    let d3 = (num / 10) % 10;
    let d4 = num % 10;
    
    (d1 == d2 && d2 == d3) || (d2 == d3 && d3 == d4)
}
// </vc-code>


}

fn main() {}