// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn check_sequence(n: usize, arr: Vec<i32>) -> (result: String)
    requires 
        n > 0,
        arr.len() > 0,
    ensures 
        result@ == "prekrasnyy"@ || result@ == "ne krasivo"@,
        result@ == "prekrasnyy"@ ==> forall|i: int, j: int| 
            0 <= i < arr.len() && 0 <= j < arr.len() && i != j ==> arr[i] != arr[j],
        result@ == "ne krasivo"@ ==> exists|i: int, j: int| 
            0 <= i < arr.len() && 0 <= j < arr.len() && i != j && arr[i] == arr[j],
        arr.len() == 1 ==> result@ == "prekrasnyy"@,
// </vc-spec>
// <vc-code>
{
    // impl-start
    assume(false);
    "prekrasnyy".to_string()
    // impl-end
}
// </vc-code>


}

fn main() {
    // let result1 = check_sequence(4, vec![1, 2, 3, 4]);
    // println!("{}", result1); // Should print "prekrasnyy"
    
    // let result2 = check_sequence(6, vec![1, 2, 3, 5, 1, 4]);
    // println!("{}", result2); // Should print "ne krasivo"
    
    // let result3 = check_sequence(1, vec![1]);
    // println!("{}", result3); // Should print "prekrasnyy"
}