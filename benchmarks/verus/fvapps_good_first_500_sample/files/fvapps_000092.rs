// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn min_time_to_send_presents(n: nat, m: nat, stack: Vec<nat>, send_list: Vec<nat>) -> (result: nat)
    requires 
        n > 0,
        n <= 100000,
        stack.len() == n,
        m <= n,
        send_list.len() == m,
        forall|i: int| 0 <= i < stack.len() ==> 1 <= stack[i] && stack[i] <= n,
        forall|i: int| 0 <= i < send_list.len() ==> 1 <= send_list[i] && send_list[i] <= n,
        // All elements in stack are unique
        forall|i: int, j: int| 0 <= i < stack.len() && 0 <= j < stack.len() && i != j ==> stack[i] != stack[j],
        // All elements in send_list are unique  
        forall|i: int, j: int| 0 <= i < send_list.len() && 0 <= j < send_list.len() && i != j ==> send_list[i] != send_list[j],
    ensures
        // Identity permutation takes n seconds
        (stack@ == send_list@ ==> result == n),
        // Reverse order takes at least as long as identity order
        result >= m,
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
    // let result1 = min_time_to_send_presents(3, 3, vec![3, 1, 2], vec![3, 2, 1]);
    // println!("Result 1: {}", result1); // Should be 5
    
    // let result2 = min_time_to_send_presents(7, 2, vec![2, 1, 7, 3, 4, 5, 6], vec![3, 1]);
    // println!("Result 2: {}", result2); // Should be 8
}