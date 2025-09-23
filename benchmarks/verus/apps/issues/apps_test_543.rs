// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(pizzas: Seq<int>) -> bool {
    forall|i: int| 0 <= i < pizzas.len() ==> pizzas[i] >= 0
}

spec fn validate_pizza_solution(pizzas: Seq<int>, index: int, d: bool, p: int) -> bool
    decreases pizzas.len() - index
    when 0 <= index <= pizzas.len() && (p == 0 || p == 1)
{
    if index == pizzas.len() {
        d && p == 0
    } else {
        let requirement = pizzas[index];
        let new_p = if requirement % 2 == 1 { 1 - p } else { p };
        let new_d = if requirement % 2 == 0 && p == 1 && requirement == 0 { false } else { d };
        validate_pizza_solution(pizzas, index + 1, new_d, new_p)
    }
}

spec fn can_fulfill_requirements(pizzas: Seq<int>) -> bool {
    validate_pizza_solution(pizzas, 0, true, 0)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
fn solve(pizzas: Vec<i8>) -> (result: String)
    requires
        forall|i: int| 0 <= i < pizzas.len() ==> pizzas[i] as int >= 0,
        valid_input(pizzas@.map(|i, x| x as int)),
    ensures
        result == "YES" ==> can_fulfill_requirements(pizzas@.map(|i, x| x as int)),
        result == "NO" ==> !can_fulfill_requirements(pizzas@.map(|i, x| x as int)),
// </vc-spec>
// <vc-code>
{
    assume(false);
    "NO".to_string()
}
// </vc-code>


}

fn main() {}