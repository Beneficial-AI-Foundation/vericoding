// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a: int) -> bool {
    1 <= a <= 40
}

spec fn presidents() -> Seq<&'static str> {
    seq![
        "Washington", "Adams", "Jefferson", "Madison", "Monroe", "Adams", "Jackson", 
        "Van Buren", "Harrison", "Tyler", "Polk", "Taylor", "Fillmore", "Pierce", 
        "Buchanan", "Lincoln", "Johnson", "Grant", "Hayes", "Garfield", "Arthur", 
        "Cleveland", "Harrison", "Cleveland", "McKinley", "Roosevelt", "Taft", 
        "Wilson", "Harding", "Coolidge", "Hoover", "Roosevelt", "Truman", 
        "Eisenhower", "Kennedy", "Johnson", "Nixon", "Ford", "Carter", "Reagan"
    ]
}
// </vc-preamble>

// <vc-helpers>
const PRESIDENTS: [&'static str; 40] = [
    "Washington", "Adams", "Jefferson", "Madison", "Monroe", "Adams", "Jackson", 
    "Van Buren", "Harrison", "Tyler", "Polk", "Taylor", "Fillmore", "Pierce", 
    "Buchanan", "Lincoln", "Johnson", "Grant", "Hayes", "Garfield", "Arthur", 
    "Cleveland", "Harrison", "Cleveland", "McKinley", "Roosevelt", "Taft", 
    "Wilson", "Harding", "Coolidge", "Hoover", "Roosevelt", "Truman", 
    "Eisenhower", "Kennedy", "Johnson", "Nixon", "Ford", "Carter", "Reagan"
];
// </vc-helpers>

// <vc-spec>
fn solve(a: i8) -> (result: &'static str)
    requires valid_input(a as int)
    ensures result == presidents()[(a as int) - 1]
// </vc-spec>
// <vc-code>
{
    // The `requires` clause `1 <= a <= 40` ensures that `a-1` is between 0 and 39.
    // Therefore, the cast to `usize` is safe and the index is in bounds.
    let idx = (a - 1) as usize;

    // Verus is able to prove that `PRESIDENTS.view() == presidents()`
    // because both are defined with the same literal values.
    // This allows it to prove the `ensures` clause.
    PRESIDENTS[idx]
}
// </vc-code>


}

fn main() {}