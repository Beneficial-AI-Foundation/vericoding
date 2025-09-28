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

// </vc-helpers>

// <vc-spec>
fn solve(a: Vec<char>, b: Vec<char>, c: Vec<char>) -> (result: char)
    requires valid_input(a@, b@, c@)
    ensures valid_winner(result)
// </vc-spec>
// <vc-code>
{
    let mut current_player: char = 'a';
    let mut a_index: usize = 0;
    let mut b_index: usize = 0;
    let mut c_index: usize = 0;
    
    loop
        invariant
            current_player == 'a' || current_player == 'b' || current_player == 'c',
            a_index <= a.len(),
            b_index <= b.len(),
            c_index <= c.len(),
            valid_input(a@, b@, c@),
        decreases
            a.len() - a_index + b.len() - b_index + c.len() - c_index,
    {
        if current_player == 'a' {
            if a_index >= a.len() {
                return 'A';
            }
            current_player = a[a_index];
            a_index = a_index + 1;
        } else if current_player == 'b' {
            if b_index >= b.len() {
                return 'B';
            }
            current_player = b[b_index];
            b_index = b_index + 1;
        } else {
            if c_index >= c.len() {
                return 'C';
            }
            current_player = c[c_index];
            c_index = c_index + 1;
        }
    }
}
// </vc-code>


}

fn main() {}