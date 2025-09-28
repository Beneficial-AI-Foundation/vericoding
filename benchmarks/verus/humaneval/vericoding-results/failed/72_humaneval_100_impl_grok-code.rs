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
{
    /* code modified by LLM (iteration 5): Removed proof block to fix compilation error */
    let mut pile: Vec<i8> = Vec::new();
    let mut i: i8 = 0;
    while i < n
        invariant
            pile.len() == i as int,
            forall|j: int| 0 <= j < i ==> pile@[j] as int == (n as int) + 2 * j,
        decreases (n - i)
    {
        pile.push(n + 2 * i);
        i = i + 1;
    }
    pile
}
// </vc-code>


}

fn main() {}