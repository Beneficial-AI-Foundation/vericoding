// <vc-preamble>
use vstd::prelude::*;

verus! {

spec fn valid_input(n: int) -> bool {
    n > 0
}

spec fn valid_pile(pile: Seq<int>, n: int) -> bool {
    &&& pile.len() == n
    &&& (n > 0 ==> pile.len() > 0 && pile[0] == n)
    &&& (forall|i: int| 0 <= i < pile.len() ==> pile[i] == n + 2 * i)
    &&& (forall|i: int| 0 <= i < pile.len() - 1 ==> #[trigger] pile.index(i + 1) == pile.index(i) + 2)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): No helpers needed */
// </vc-helpers>

// <vc-spec>
fn make_a_pile(n: i8) -> (pile: Vec<i8>)
    requires valid_input(n as int)
    ensures valid_pile(pile@.map(|i: int, x: i8| x as int), n as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Corrected type issues: converted loop counter `i` to `usize` for concrete operations and casted `n` to `usize` for loop bounds and `i` to `int` within `N_int` expression */
{
    let mut pile: Vec<i8> = Vec::new();
    let ghost N_int: int = n as int;

    let mut i: usize = 0;
    while (i as int) < (n as int)
        invariant
            0 <= i as int <= n as int,
            pile.len() == i,
            pile.len() <= (n as usize),
            forall|j: int| 0 <= j < i as int ==> pile@[j as int] == (N_int + 2 * j) as i8,
            (n as int > 0 ==> pile.len() > 0 ==> pile@[0] == n as i8),
            forall|j: int| 0 <= j < i as int - 1 ==> pile@[j as int + 1] == pile@[j as int] + 2,
        decreases (n as int) - (i as int)
    {
        let current_val = (N_int + 2 * (i as int)) as i8;

        if (i == 0) {
            assert(current_val == n as i8);
        }

        pile.push(current_val);

        proof {
            if (i > 0) {
                assert((i as int) - 1 >= 0);
                assert(pile@[(i as int) - 1] == (N_int + 2 * ((i as int) - 1)) as i8);
                assert(pile@[(i as int)] == (N_int + 2 * (i as int)) as i8);
                assert(pile@[(i as int)] == pile@[(i as int) - 1] + 2);
            }
        }
        i = i + 1;
    }

    pile
}
// </vc-code>


}

fn main() {}