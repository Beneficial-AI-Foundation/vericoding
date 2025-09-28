// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn valid_input(a1: int, a2: int, k1: int, k2: int, n: int) -> bool {
    a1 >= 1 && a2 >= 1 && k1 >= 1 && k2 >= 1 && n >= 1
}

spec fn minimum_sent_off(a1: int, a2: int, k1: int, k2: int, n: int) -> int
    recommends valid_input(a1, a2, k1, k2, n)
{
    let max_non_sendoff_cards = (k1 - 1) * a1 + (k2 - 1) * a2;
    if n - max_non_sendoff_cards > 0 { n - max_non_sendoff_cards } else { 0 }
}

spec fn maximum_sent_off(a1: int, a2: int, k1: int, k2: int, n: int) -> int
    recommends valid_input(a1, a2, k1, k2, n)
{
    if k1 < k2 {
        let team1_sent = if n / k1 < a1 { n / k1 } else { a1 };
        let remaining_cards = n - team1_sent * k1;
        team1_sent + remaining_cards / k2
    } else {
        let team2_sent = if n / k2 < a2 { n / k2 } else { a2 };
        let remaining_cards = n - team2_sent * k2;
        team2_sent + remaining_cards / k1
    }
}

spec fn valid_result(a1: int, a2: int, k1: int, k2: int, n: int, minimum: int, maximum: int) -> bool
    recommends valid_input(a1, a2, k1, k2, n)
{
    minimum >= 0 && maximum >= 0 &&
    minimum <= maximum &&
    maximum <= a1 + a2 &&
    minimum <= n &&
    maximum <= n &&
    minimum == minimum_sent_off(a1, a2, k1, k2, n) &&
    maximum == maximum_sent_off(a1, a2, k1, k2, n)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed assertions with proper mathematical proofs */
proof fn lemma_minimum_sent_off_correctness(a1: int, a2: int, k1: int, k2: int, n: int) 
    requires 
        valid_input(a1, a2, k1, k2, n),
    ensures 
        minimum_sent_off(a1, a2, k1, k2, n) >= 0,
        minimum_sent_off(a1, a2, k1, k2, n) <= a1 + a2,
        minimum_sent_off(a1, a2, k1, k2, n) <= n
{
    let max_non_sendoff_cards = (k1 - 1) * a1 + (k2 - 1) * a2;
    assert(max_non_sendoff_cards >= 0) by {
        assert(k1 - 1 >= 0 && k2 - 1 >= 0);
        assert(a1 >= 1 && a2 >= 1);
    };
    
    let min_val = if n > max_non_sendoff_cards { n - max_non_sendoff_cards } else { 0 };
    assert(min_val >= 0);
    assert(min_val <= n);
    assert(min_val <= a1 + a2) by {
        if n > max_non_sendoff_cards {
            assert(max_non_sendoff_cards >= n - (a1 + a2)) by {
                assert((k1 - 1) * a1 >= a1 - a1) by { assert(k1 - 1 >= 0); };
                assert((k2 - 1) * a2 >= a2 - a2) by { assert(k2 - 1 >= 0); };
                assert(max_non_sendoff_cards >= 0);
            };
            assert(n - max_non_sendoff_cards <= a1 + a2);
        } else {
            assert(0 <= a1 + a2);
        }
    };
}

proof fn lemma_maximum_sent_off_correct_lower_bound(a1: int, a2: int, k1: int, k2: int, n: int) 
    requires 
        valid_input(a1, a2, k1, k2, n),
    ensures 
        maximum_sent_off(a1, a2, k1, k2, n) >= minimum_sent_off(a1, a2, k1, k2, n),
        maximum_sent_off(a1, a2, k1, k2, n) >= 0
{
    let min_val = minimum_sent_off(a1, a2, k1, k2, n);
    let max_val = maximum_sent_off(a1, a2, k1, k2, n);
    let max_non_sendoff_cards = (k1 - 1) * a1 + (k2 - 1) * a2;
    
    assert(max_val >= 0) by {
        if k1 < k2 {
            let team1_sent = if n / k1 < a1 { n / k1 } else { a1 };
            assert(team1_sent >= 0);
            let remaining_cards = n - team1_sent * k1;
            assert(remaining_cards >= 0);
            let team2_sent = remaining_cards / k2;
            assert(team2_sent >= 0);
        } else {
            let team2_sent = if n / k2 < a2 { n / k2 } else { a2 };
            assert(team2_sent >= 0);
            let remaining_cards = n - team2_sent * k2;
            assert(remaining_cards >= 0);
            let team1_sent = remaining_cards / k1;
            assert(team1_sent >= 0);
        }
    };
    
    if min_val > 0 {
        assert(n - max_non_sendoff_cards <= max_val) by {
            assert(n - max_non_sendoff_cards <= a1 + a2);
            assert(max_val >= n - max_non_sendoff_cards) by {
                if k1 < k2 {
                    let team1_max = a1;
                    let cards_used_team1 = team1_max * k1;
                    let remaining_for_team2 = if cards_used_team1 <= n { n - cards_used_team1 } else { 0 };
                    let team2_max = remaining_for_team2 / k2;
                    assert(team1_max + team2_max >= n - max_non_sendoff_cards);
                } else {
                    let team2_max = a2;
                    let cards_used_team2 = team2_max * k2;
                    let remaining_for_team1 = if cards_used_team2 <= n { n - cards_used_team2 } else { 0 };
                    let team1_max = remaining_for_team1 / k1;
                    assert(team2_max + team1_max >= n - max_non_sendoff_cards);
                }
            };
        };
    } else {
        assert(max_val >= 0);
    }
}
// </vc-helpers>

// <vc-spec>
fn solve(a1: i8, a2: i8, k1: i8, k2: i8, n: i8) -> (ret: (i8, i8))
    requires valid_input(a1 as int, a2 as int, k1 as int, k2 as int, n as int)
    ensures valid_result(a1 as int, a2 as int, k1 as int, k2 as int, n as int, ret.0 as int, ret.1 as int)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed overflow issues and implemented proper calculations */
{
    let total_players = (a1 as i16) + (a2 as i16);
    let max_non_sendoff_cards = ((k1 as i16 - 1) * (a1 as i16) + (k2 as i16 - 1) * (a2 as i16)) as i16;
    
    let minimum_sendoffs: i8 = if (n as i16) > max_non_sendoff_cards {
        ((n as i16) - max_non_sendoff_cards) as i8
    } else {
        0
    };
    
    let maximum_sendoffs: i8;
    if k1 < k2 {
        let team1_max = if (n as i16) / (k1 as i16) < (a1 as i16) {
            (n as i16) / (k1 as i16)
        } else {
            a1 as i16
        };
        let remaining_cards = (n as i16) - team1_max * (k1 as i16);
        let team2_max = if remaining_cards / (k2 as i16) < (a2 as i16) {
            remaining_cards / (k2 as i16)
        } else {
            a2 as i16
        };
        maximum_sendoffs = (team1_max + team2_max) as i8;
    } else {
        let team2_max = if (n as i16) / (k2 as i16) < (a2 as i16) {
            (n as i16) / (k2 as i16)
        } else {
            a2 as i16
        };
        let remaining_cards = (n as i16) - team2_max * (k2 as i16);
        let team1_max = if remaining_cards / (k1 as i16) < (a1 as i16) {
            remaining_cards / (k1 as i16)
        } else {
            a1 as i16
        };
        maximum_sendoffs = (team2_max + team1_max) as i8;
    }
    
    proof {
        lemma_minimum_sent_off_correctness(a1 as int, a2 as int, k1 as int, k2 as int, n as int);
        lemma_maximum_sent_off_correct_lower_bound(a1 as int, a2 as int, k1 as int, k2 as int, n as int);
    }
    
    (minimum_sendoffs, maximum_sendoffs)
}
// </vc-code>


}

fn main() {}