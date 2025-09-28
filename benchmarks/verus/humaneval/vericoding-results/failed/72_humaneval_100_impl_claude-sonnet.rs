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
/* helper modified by LLM (iteration 5): strengthened preconditions to ensure arithmetic bounds hold */
proof fn lemma_pile_property(pile: Seq<int>, n: int, i: int)
    requires
        valid_pile(pile, n),
        0 <= i < pile.len(),
    ensures pile[i] == n + 2 * i
{
}

proof fn lemma_pile_length(n: int)
    requires n > 0
    ensures n == n
{
}

proof fn lemma_arithmetic_bounds(n: i8, i: i8)
    requires
        0 <= i < n,
        n > 0,
        n <= 63,
    ensures
        2 * i <= 254,
        n + 2 * i <= 127,
{
}
// </vc-helpers>

// <vc-spec>
fn make_a_pile(n: i8) -> (pile: Vec<i8>)
    requires valid_input(n as int)
    ensures valid_pile(pile@.map(|i: int, x: i8| x as int), n as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): added precondition check for arithmetic bounds */
    let mut pile: Vec<i8> = Vec::new();
    let mut i: i8 = 0;
    
    while i < n
        invariant
            0 <= i <= n,
            pile@.len() == i,
            forall|j: int| 0 <= j < i ==> pile@[j] as int == (n as int + 2 * j),
            n <= 63,
            i <= 127,
        decreases n - i
    {
        proof {
            lemma_arithmetic_bounds(n, i);
        }
        let value = n + 2 * i;
        pile.push(value);
        i = i + 1;
    }
    
    pile
}
// </vc-code>


}

fn main() {}