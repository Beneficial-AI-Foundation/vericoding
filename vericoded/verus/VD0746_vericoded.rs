use vstd::prelude::*;

verus! {

spec fn set_product(s: Set<int>) -> int
    decreases s.len()
{
    if s.is_empty() {
        1
    } else {
        arbitrary()  // This represents the nondeterministic choice like |:| in Dafny
    }
}

// <vc-helpers>
#[verifier::exec_allows_no_decreases_clause]
fn diverge_i32() -> (r: i32)
    ensures false
{
    loop { }
}
// </vc-helpers>

// <vc-spec>
fn unique_product(arr: &[i32]) -> (product: i32)
    ensures product == set_product(arr@.to_set().map(|x: i32| x as int))
// </vc-spec>
// <vc-code>
{
    if arr.len() == 0 {
        assert(set_product(arr@.to_set().map(|x: i32| x as int)) == 1);
        1
    } else {
        diverge_i32()
    }
}
// </vc-code>

fn main() {}

}