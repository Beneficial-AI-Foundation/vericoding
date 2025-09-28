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
/* helper modified by LLM (iteration 4): fixed by naming return value in function signature for ensures clause */
fn get_presidents() -> (result: Vec<&'static str>)
    ensures result@ == presidents()
{
    let mut v = Vec::new();
    v.push("Washington");
    v.push("Adams");
    v.push("Jefferson");
    v.push("Madison");
    v.push("Monroe");
    v.push("Adams");
    v.push("Jackson");
    v.push("Van Buren");
    v.push("Harrison");
    v.push("Tyler");
    v.push("Polk");
    v.push("Taylor");
    v.push("Fillmore");
    v.push("Pierce");
    v.push("Buchanan");
    v.push("Lincoln");
    v.push("Johnson");
    v.push("Grant");
    v.push("Hayes");
    v.push("Garfield");
    v.push("Arthur");
    v.push("Cleveland");
    v.push("Harrison");
    v.push("Cleveland");
    v.push("McKinley");
    v.push("Roosevelt");
    v.push("Taft");
    v.push("Wilson");
    v.push("Harding");
    v.push("Coolidge");
    v.push("Hoover");
    v.push("Roosevelt");
    v.push("Truman");
    v.push("Eisenhower");
    v.push("Kennedy");
    v.push("Johnson");
    v.push("Nixon");
    v.push("Ford");
    v.push("Carter");
    v.push("Reagan");
    v
}
// </vc-helpers>

// <vc-spec>
fn solve(a: i8) -> (result: &'static str)
    requires valid_input(a as int)
    ensures result == presidents()[(a as int) - 1]
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 4): awaiting verification after fixing compilation */
    let v = get_presidents();
    let index = (a as usize) - 1;
    v[index]
}
// </vc-code>


}

fn main() {}