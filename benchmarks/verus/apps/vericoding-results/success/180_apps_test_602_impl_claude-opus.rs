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

// </vc-helpers>

// <vc-spec>
fn solve(a: i8) -> (result: &'static str)
    requires valid_input(a as int)
    ensures result == presidents()[(a as int) - 1]
// </vc-spec>
// <vc-code>
{
    let presidents_list = vec![
        "Washington", "Adams", "Jefferson", "Madison", "Monroe", "Adams", "Jackson",
        "Van Buren", "Harrison", "Tyler", "Polk", "Taylor", "Fillmore", "Pierce",
        "Buchanan", "Lincoln", "Johnson", "Grant", "Hayes", "Garfield", "Arthur",
        "Cleveland", "Harrison", "Cleveland", "McKinley", "Roosevelt", "Taft",
        "Wilson", "Harding", "Coolidge", "Hoover", "Roosevelt", "Truman",
        "Eisenhower", "Kennedy", "Johnson", "Nixon", "Ford", "Carter", "Reagan"
    ];
    
    let index = (a - 1) as usize;
    
    proof {
        assert(0 <= index < 40);
        assert(presidents_list@.len() == 40);
        assert(presidents_list@[index as int] == presidents()[index as int]);
    }
    
    presidents_list[index]
}
// </vc-code>


}

fn main() {}