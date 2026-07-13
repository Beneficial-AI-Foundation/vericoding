// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
spec fn sum_vec(l: Seq<nat>) -> nat
    decreases l.len()
{
    if l.len() == 0 {
        0
    } else {
        l[0] + sum_vec(l.skip(1))
    }
}

spec fn minimum_vec(l: Seq<nat>) -> nat 
    decreases l.len()
{
    if l.len() == 0 {
        0
    } else if l.len() == 1 {
        l[0]
    } else {
        let rest_min = minimum_vec(l.skip(1));
        if l[0] < rest_min { l[0] } else { rest_min }
    }
}
// </vc-helpers>

// <vc-spec>
spec fn base_satisfied(customers: Seq<nat>, grumpy: Seq<nat>) -> nat
    decreases customers.len()
{
    if customers.len() == 0 || grumpy.len() == 0 {
        0
    } else {
        let current = if grumpy[0] == 0 { customers[0] } else { 0 };
        current + base_satisfied(customers.skip(1), grumpy.skip(1))
    }
}

spec fn all_zeros(grumpy: Seq<nat>) -> bool {
    forall|i: int| 0 <= i < grumpy.len() ==> grumpy[i] == 0
}

fn max_satisfied(customers: Vec<nat>, grumpy: Vec<nat>, x: nat) -> (result: nat)
    requires
        customers.len() > 0,
        grumpy.len() == customers.len(),
        x > 0,
        forall|i: int| 0 <= i < customers.len() ==> customers[i] <= 1000,
        forall|i: int| 0 <= i < grumpy.len() ==> grumpy[i] <= 1,
    ensures
        result >= base_satisfied(customers@, grumpy@),
        result <= sum_vec(customers@),
        all_zeros(grumpy@) ==> result == sum_vec(customers@),
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
    // let customers1 = vec![1, 0, 1, 2, 1, 1, 7, 5];
    // let grumpy1 = vec![0, 1, 0, 1, 0, 1, 0, 1];
    // let result1 = max_satisfied(customers1, grumpy1, 3);
    // println!("Test 1 result: {}", result1);
    
    // let customers2 = vec![1];
    // let grumpy2 = vec![0];
    // let result2 = max_satisfied(customers2, grumpy2, 1);
    // println!("Test 2 result: {}", result2);
    
    // let customers3 = vec![2, 4, 1, 4, 1];
    // let grumpy3 = vec![1, 1, 1, 1, 1];
    // let result3 = max_satisfied(customers3, grumpy3, 2);
    // println!("Test 3 result: {}", result3);
}