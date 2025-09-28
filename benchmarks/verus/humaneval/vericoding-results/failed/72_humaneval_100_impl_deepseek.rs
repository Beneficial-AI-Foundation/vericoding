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
proof fn pile_at(i: nat, n: nat) -> int {
    n as int + 2 * (i as int)
}

proof fn pile_properties(n: nat)
    requires
        n > 0,
    ensures
        valid_pile(Seq::new(n as nat, |i: nat| pile_at(i, n)), n as int),
    decreases n,
{
    if n > 0 {
        let s = Seq::new(n as nat, |i: nat| pile_at(i, n));
        assert forall|i: int| 0 <= i < s.len() implies s[i] == (n as int) + 2 * i by {
            assert(s[i] == pile_at(i as nat, n));
        };
        assert forall|i: int| 0 <= i < s.len() - 1 implies s[i + 1] == s[i] + 2 by {
            assert(s[i] == (n as int) + 2 * i);
            assert(s[i + 1] == (n as int) + 2 * (i + 1));
            assert((n as int) + 2 * (i + 1) == ((n as int) + 2 * i) + 2);
        };
        assert(s[0] == n as int);
        assert(s.len() == n as int);
    }
}
// </vc-helpers>

// <vc-spec>
fn make_a_pile(n: i8) -> (pile: Vec<i8>)
    requires valid_input(n as int)
    ensures valid_pile(pile@.map(|i: int, x: i8| x as int), n as int)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): fix int/nat casting and sequence indexing issues */
    let mut pile = Vec::new();
    let mut i: usize = 0;
    let n_usize = n as usize;
    while i < n_usize
        invariant
            pile@.len() == i,
            i <= n_usize,
            forall|j: int| 0 <= j < pile@.len() ==> #[trigger] pile@[j] == (n as int + 2 * j) as i8,
    {
        let value = (n as int + 2 * (i as int)) as i8;
        pile.push(value);
        i += 1;
    }
    proof {
        pile_properties(n as nat);
    }
    pile
}
// </vc-code>


}

fn main() {}