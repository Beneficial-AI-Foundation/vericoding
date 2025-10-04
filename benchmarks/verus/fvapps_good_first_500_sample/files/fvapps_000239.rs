// <vc-preamble>
use vstd::prelude::*;

verus! {
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
spec fn is_in_list(val: nat, list: Seq<nat>) -> bool {
    exists|i: int| 0 <= i < list.len() && list[i] == val
}

spec fn same_front_back(fronts: Seq<nat>, backs: Seq<nat>, val: nat) -> bool {
    exists|i: int| 0 <= i < fronts.len() && fronts[i] == backs[i] && fronts[i] == val
}

fn flipgame(fronts: Vec<nat>, backs: Vec<nat>) -> (result: nat)
    requires fronts.len() == backs.len(),
    ensures
        result != 0 ==> is_in_list(result, fronts@) || is_in_list(result, backs@),
        result != 0 ==> !same_front_back(fronts@, backs@, result),
        result != 0 ==> forall|n: nat| #[trigger] is_in_list(n, fronts@) || is_in_list(n, backs@) ==>
                            !same_front_back(fronts@, backs@, n) ==> result <= n,
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
    // let test1 = flipgame(vec![1, 2, 4, 4, 7], vec![1, 3, 4, 1, 3]);
    // assert(test1 == 2);
    
    // let test2 = flipgame(vec![1, 1], vec![1, 1]);
    // assert(test2 == 0);
    
    // let test3 = flipgame(vec![1, 2], vec![2, 1]);
    // assert(test3 == 1);
}