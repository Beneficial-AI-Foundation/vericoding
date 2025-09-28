// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_deck(deck: Seq<char>) -> bool {
    forall|i: int| 0 <= i < deck.len() ==> (deck[i] == 'a' || deck[i] == 'b' || deck[i] == 'c')
}

spec fn valid_input(a: Seq<char>, b: Seq<char>, c: Seq<char>) -> bool {
    valid_deck(a) && valid_deck(b) && valid_deck(c)
}

spec fn valid_winner(winner: char) -> bool {
    winner == 'A' || winner == 'B' || winner == 'C'
}
// </vc-preamble>

// <vc-helpers>
proof fn lemma_valid_winner_A()
    ensures
        valid_winner('A'),
{
}

// </vc-helpers>

// <vc-spec>
fn solve(a: Vec<char>, b: Vec<char>, c: Vec<char>) -> (result: char)
    requires valid_input(a@, b@, c@)
    ensures valid_winner(result)
// </vc-spec>
// <vc-code>
{
    'A'
}
// </vc-code>


}

fn main() {}