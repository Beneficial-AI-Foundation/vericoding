// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn will_friend_request(age_a: nat, age_b: nat) -> bool {
    age_a != age_b &&
    !(age_b <= (age_a / 2) + 7) &&
    !(age_b > age_a) &&
    !(age_b > 100 && age_a < 100)
}

fn num_friend_requests(ages: Vec<nat>) -> (result: nat)
    requires 
        ages.len() >= 1,
        ages.len() <= 20000,
        forall|i: int| #[trigger] ages[i] == ages[i] && 0 <= i < ages.len() ==> 1 <= ages[i] <= 120,
    ensures 
        result >= 0,
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
    // println!("{}", num_friend_requests(vec![16, 16]));
    // println!("{}", num_friend_requests(vec![16, 17, 18]));  
    // println!("{}", num_friend_requests(vec![20, 30, 100, 110, 120]));
}