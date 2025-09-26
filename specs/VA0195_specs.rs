// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(y: int) -> bool {
    1000 <= y <= 9000
}

spec fn has_distinct_digits(n: int) -> bool {
    let digits = number_to_digits(n);
    all_distinct(digits)
}

spec fn number_to_digits(n: int) -> Seq<int> {
    if n == 0 { seq![0] }
    else if n > 0 { number_to_digits_helper(n, seq![]) }
    else { number_to_digits_helper(-n, seq![]) }
}

spec fn number_to_digits_helper(n: int, acc: Seq<int>) -> Seq<int>
    decreases n when n >= 0
{
    if n == 0 { acc }
    else { number_to_digits_helper(n / 10, seq![n % 10].add(acc)) }
}

spec fn all_distinct(digits: Seq<int>) -> bool {
    forall|i: int, j: int| 0 <= i < j < digits.len() ==> digits[i] != digits[j]
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(y: i8) -> (result: i8)
    requires valid_input(y as int)
    ensures 
        result as int > y as int,
        has_distinct_digits(result as int),
        forall|n: int| y as int < n && n < result as int ==> !has_distinct_digits(n)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}