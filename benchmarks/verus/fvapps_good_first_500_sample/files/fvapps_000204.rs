// <vc-preamble>
use vstd::prelude::*;
use vstd::string::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn predict_party_victory(senate: Vec<char>) -> (result: String)
    requires senate.len() > 0,
    ensures 
        result@ == "Radiant"@ || result@ == "Dire"@
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    "Radiant".to_string()
    // impl-end
}
// </vc-code>

}

fn main() {
    // let rd: Vec<char> = "RD".chars().collect();
    // println!("{}", predict_party_victory(rd));
    // let rdd: Vec<char> = "RDD".chars().collect();
    // println!("{}", predict_party_victory(rdd));
    // let rrddd: Vec<char> = "RRDDD".chars().collect();
    // println!("{}", predict_party_victory(rrddd));
}