// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn largest_number(l: Vec<nat>) -> (result: String)
    ensures
        l.len() == 0 ==> result.view() == seq!['0'],
        l@ == seq![0nat] ==> result.view() == seq!['0'],
        l@ == seq![0nat, 0nat] ==> result.view() == seq!['0'],
        l@ == seq![10nat, 2nat] ==> result.view() == seq!['2', '1', '0'],
        l@ == seq![3nat, 30nat, 34nat, 5nat, 9nat] ==> result.view() == seq!['9', '5', '3', '4', '3', '3', '0']
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    unreached()
    // impl-end
}
// </vc-code>


}

fn main() {
    // let result1 = largest_number(vec![10, 2]);
    // println!("{}", result1); // Should print "210"
    
    // let result2 = largest_number(vec![3, 30, 34, 5, 9]);
    // println!("{}", result2); // Should print "9534330"
    
    // let result3 = largest_number(vec![0, 0]);
    // println!("{}", result3); // Should print "0"
}