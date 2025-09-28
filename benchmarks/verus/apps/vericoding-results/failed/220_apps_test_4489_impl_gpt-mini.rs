// <vc-preamble>
use vstd::prelude::*;

verus! {
spec fn count_occurrences(cards: Seq<&str>, target: &str) -> int
    decreases cards.len()
{
    if cards.len() == 0 {
        0
    } else if cards[0] == target {
        1 + count_occurrences(cards.subrange(1, cards.len() as int), target)
    } else {
        count_occurrences(cards.subrange(1, cards.len() as int), target)
    }
}

spec fn get_unique_strings(all_strings: Seq<&str>) -> Seq<&str>
    decreases all_strings.len()
{
    if all_strings.len() == 0 {
        Seq::empty()
    } else {
        let rest_unique = get_unique_strings(all_strings.subrange(1, all_strings.len() as int));
        if rest_unique.contains(all_strings[0]) {
            rest_unique
        } else {
            seq![all_strings[0]].add(rest_unique)
        }
    }
}

spec fn max_net_earnings(blue_cards: Seq<&str>, red_cards: Seq<&str>) -> int {
    let unique_blue = get_unique_strings(blue_cards);
    max_net_earnings_helper(unique_blue, blue_cards, red_cards, 0, 0)
}

spec fn max_net_earnings_helper(unique_blue: Seq<&str>, blue_cards: Seq<&str>, red_cards: Seq<&str>, index: int, current_max: int) -> int
    decreases unique_blue.len() - index
{
    if index >= unique_blue.len() {
        current_max
    } else {
        let s = unique_blue[index];
        let blue_count = count_occurrences(blue_cards, s);
        let red_count = count_occurrences(red_cards, s);
        let net = blue_count - red_count;
        let new_max = if net > current_max { net } else { current_max };
        max_net_earnings_helper(unique_blue, blue_cards, red_cards, index + 1, new_max)
    }
}

proof fn count_occurrences_non_negative(cards: Seq<&str>, target: &str)
    ensures count_occurrences(cards, target) >= 0
    decreases cards.len()
{
    if cards.len() == 0 {
    } else if cards[0] == target {
        count_occurrences_non_negative(cards.subrange(1, cards.len() as int), target);
    } else {
        count_occurrences_non_negative(cards.subrange(1, cards.len() as int), target);
    }
}

proof fn max_net_earnings_non_negative(blue_cards: Seq<&str>, red_cards: Seq<&str>)
    ensures max_net_earnings(blue_cards, red_cards) >= 0
{
    let unique_blue = get_unique_strings(blue_cards);
    max_net_earnings_helper_non_negative(unique_blue, blue_cards, red_cards, 0, 0);
}

proof fn max_net_earnings_helper_non_negative(unique_blue: Seq<&str>, blue_cards: Seq<&str>, red_cards: Seq<&str>, index: int, current_max: int)
    requires 
        0 <= index <= unique_blue.len(),
        current_max >= 0
    ensures max_net_earnings_helper(unique_blue, blue_cards, red_cards, index, current_max) >= current_max
    decreases unique_blue.len() - index
{
    if index >= unique_blue.len() {
    } else {
        let s = unique_blue[index];
        let blue_count = count_occurrences(blue_cards, s);
        let red_count = count_occurrences(red_cards, s);
        let net = blue_count - red_count;
        let new_max = if net > current_max { net } else { current_max };
        max_net_earnings_helper_non_negative(unique_blue, blue_cards, red_cards, index + 1, new_max);
    }
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): max-over-from recursive spec */
spec fn max_over_from(blue: Seq<&str>, red: Seq<&str>, idx: int, curr: int) -> int
    decreases blue.len() - idx
{
    if idx >= blue.len() {
        curr
    } else {
        let s = blue[idx];
        let net = count_occurrences(blue, s) - count_occurrences(red, s);
        let new = if net > curr { net } else { curr };
        max_over_from(blue, red, idx + 1, new)
    }
}

/* helper modified by LLM (iteration 5): entry point for max-over computation */
spec fn max_over_indices(blue: Seq<&str>, red: Seq<&str>) -> int {
    max_over_from(blue, red, 0, 0)
}

/* helper modified by LLM (iteration 5): concrete counting over Vec */
fn count_occurrences_vec(cards: &Vec<&str>, target: &str) -> int
    ensures
        result == count_occurrences(cards@, target),
        result >= 0
    decreases cards.len()
{
    let n: int = cards.len() as int;
    let mut j: int = 0;
    let mut res: int = 0;
    while j < n
        invariant
            0 <= j <= n,
            res == count_occurrences(cards@.subrange(0, j), target),
        decreases n - j
    {
        if cards[j as usize] == target {
            res = res + 1;
        }
        j = j + 1;
    }
    res
}

/* helper modified by LLM (iteration 5): concrete max-over for Vec */
fn max_over_indices_vec(blue: &Vec<&str>, red: &Vec<&str>) -> int
    ensures
        result == max_over_indices(blue@, red@)
    decreases blue.len()
{
    let n: int = blue.len() as int;
    let mut j: int = 0;
    let mut cur: int = 0;
    while j < n
        invariant
            0 <= j <= n,
            max_over_from(blue@, red@, 0, 0) == max_over_from(blue@, red@, j, cur),
        decreases n - j
    {
        let s = blue[j as usize];
        let bcount = count_occurrences_vec(blue, s);
        let rcount = count_occurrences_vec(red, s);
        let net = bcount - rcount;
        if net > cur {
            cur = net;
        }
        j = j + 1;
    }
    cur
}

/* helper modified by LLM (iteration 5): relate iterative max to spec max_net_earnings */
proof fn max_over_indices_eq_max_net_earnings(blue: Seq<&str>, red: Seq<&str>)
    ensures max_over_indices(blue, red) == max_net_earnings(blue, red)
    decreases blue.len()
{
    if blue.len() == 0 {
        // both definitions yield 0 for empty blue
    } else {
        // We proceed by induction on the length of blue. Let s be first element and rest be the remainder.
        let s = blue[0];
        let rest = blue.subrange(1, blue.len());
        // IH
        max_over_indices_eq_max_net_earnings(rest, red);
        // Show that processing duplicates in blue does not change the maximum by reasoning on definitions.
        // If s is already in get_unique_strings(rest), then max over blue equals max over rest.
        if get_unique_strings(rest).contains(s) {
            // Then both max_over_indices and max_net_earnings ignore the duplicate first element
            assert(max_over_indices(blue, red) == max_over_indices(rest, red));
            assert(max_net_earnings(blue, red) == max_net_earnings(rest, red));
            assert(max_over_indices(rest, red) == max_net_earnings(rest, red));
        } else {
            // If s is new, both computations consider s exactly once; unfold definitions to relate them.
            assert(max_over_indices(blue, red) == max_over_from(blue, red, 0, 0));
            assert(max_net_earnings(blue, red) == max_net_earnings_helper(get_unique_strings(blue), blue, red, 0, 0));
            // By definition, get_unique_strings(blue) == seq![s].add(get_unique_strings(rest)) when s not in rest
            // Then max over unique strings equals taking max between net(s) and max over rest, which matches max_over_from behavior.
            assert(max_over_indices(blue, red) == max_net_earnings(blue, red));
        }
    }
}

// </vc-helpers>

// <vc-spec>
fn solve(blue_cards: Vec<&str>, red_cards: Vec<&str>) -> (result: i8)
    ensures 
        result >= 0,
        result as int == max_net_earnings(blue_cards@, red_cards@)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): compute max net earnings via concrete helpers and return as i8 */
{
    let m = max_over_indices_vec(&blue_cards, &red_cards);
    proof {
        max_over_indices_eq_max_net_earnings(blue_cards@, red_cards@);
        max_net_earnings_non_negative(blue_cards@, red_cards@);
        assert(m == max_over_indices(blue_cards@, red_cards@));
        assert(m == max_net_earnings(blue_cards@, red_cards@));
    }
    let result: i8 = m as i8;
    result
}

// </vc-code>


}

fn main() {}