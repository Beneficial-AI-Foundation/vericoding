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
// </vc-helpers>

// <vc-spec>
fn solve(blue_cards: Vec<&str>, red_cards: Vec<&str>) -> (result: i8)
    ensures 
        result >= 0,
        result as int == max_net_earnings(blue_cards@, red_cards@)
// </vc-spec>
// <vc-code>
{
    assume(false);
    unreached()
}
// </vc-code>


}

fn main() {}