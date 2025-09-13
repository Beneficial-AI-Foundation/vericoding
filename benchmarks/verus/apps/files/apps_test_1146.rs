// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: nat, m: nat, buttons: Seq<Seq<nat>>) -> bool {
    buttons.len() == n &&
    n >= 1 && m >= 1 &&
    forall|i: int| 0 <= i < n ==> forall|j: int| 0 <= j < buttons[i].len() ==> 1 <= buttons[i][j] <= m
}

spec fn union_of_all_bulbs(buttons: Seq<Seq<nat>>) -> Set<nat> {
    Set::new(|bulb: nat| exists|i: int, j: int| 0 <= i < buttons.len() && 0 <= j < buttons[i].len() && buttons[i][j] == bulb)
}

spec fn can_turn_on_all_bulbs(m: nat, buttons: Seq<Seq<nat>>) -> bool {
    union_of_all_bulbs(buttons).len() == m
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(n: nat, m: nat, buttons: Seq<Seq<nat>>) -> (result: String)
    requires 
        valid_input(n, m, buttons)
    ensures 
        result == "YES" || result == "NO",
        result == "YES" <==> can_turn_on_all_bulbs(m, buttons)
// </vc-spec>
// <vc-code>
{
    /* impl-start */
    assume(false);
    "NO".to_string()
    /* impl-end */
}
// </vc-code>


}

fn main() {}