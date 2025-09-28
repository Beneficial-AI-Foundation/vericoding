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
/* helper modified by LLM (iteration 2): changed from spec to exec function */
fn beats(x: char, y: char) -> bool {
    (x == 'a' && y == 'c') || (x == 'b' && y == 'a') || (x == 'c' && y == 'b')
}
// </vc-helpers>

// <vc-spec>
fn solve(a: Vec<char>, b: Vec<char>, c: Vec<char>) -> (result: char)
    requires valid_input(a@, b@, c@)
    ensures valid_winner(result)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): fixed loop invariants to use 2*i instead of 2*(n-i) */
{
    let mut winsA: u128 = 0;
    let mut winsB: u128 = 0;
    let mut winsC: u128 = 0;

    let mut n = a.len();
    if b.len() < n {
        n = b.len();
    }
    if c.len() < n {
        n = c.len();
    }

    let mut i = 0;
    while i < n
        invariant
            0 <= i <= n,
            n <= a@.len(),
            n <= b@.len(),
            n <= c@.len(),
            winsA as int <= 2 * i,
            winsB as int <= 2 * i,
            winsC as int <= 2 * i,
        decreases n - i
    {
        assert(i < a.len());
        assert(i < b.len());
        assert(i < c.len());

        let cardA = a[i];
        let cardB = b[i];
        let cardC = c[i];

        if cardA != cardB {
            if beats(cardA, cardB) {
                winsA += 1;
            } else {
                winsB += 1;
            }
        }

        if cardB != cardC {
            if beats(cardB, cardC) {
                winsB += 1;
            } else {
                winsC += 1;
            }
        }

        if cardC != cardA {
            if beats(cardC, cardA) {
                winsC += 1;
            } else {
                winsA += 1;
            }
        }

        i += 1;
    }

    let mut max_wins: u128 = winsA;
    if winsB > max_wins {
        max_wins = winsB;
    }
    if winsC > max_wins {
        max_wins = winsC;
    }

    if winsA == max_wins {
        'A'
    } else if winsB == max_wins {
        'B'
    } else {
        'C'
    }
}
// </vc-code>


}

fn main() {}