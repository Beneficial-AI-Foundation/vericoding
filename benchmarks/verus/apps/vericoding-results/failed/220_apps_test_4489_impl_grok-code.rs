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
/* helper modified by LLM (iteration 5): replaced == with str_to_view == will remove to fix compilation */
fn count_occurrences_exec<'a>(cards: &'a Vec<&'a str>, target: &'a str) -> usize
{
    let mut count = 0;
    let mut i = 0;
    while i < cards.len()
    {
        if vstd::string::str_to_view(cards[i]) == vstd::string::str_to_view(target)
        {
            count += 1;
        }
        i += 1;
    }
    count
}

/* helper modified by LLM (iteration 5): replaced contains on &str with contains on Seq<char> to fix compilation */
fn get_unique_blue_exec<'a>(cards: &'a Vec<&'a str>) -> Vec<&'a str>
{
    let mut uniques = Vec::new();
    let mut set: vstd::set::Set<Seq<char>> = vstd::set::Set::empty();
    for i in 0..cards.len()
    {
        let card = cards[i];
        let view = vstd::string::str_to_view(card);
        if !set.contains(view)
        {
            set = set.insert(view);
            uniques.push(card);
        }
    }
    uniques
}
// </vc-helpers>

// <vc-spec>
fn solve(blue_cards: Vec<&str>, red_cards: Vec<&str>) -> (result: i8)
    ensures 
        result >= 0,
        result as int == max_net_earnings(blue_cards@, red_cards@)
// </vc-spec>
// <vc-code>
{
    /* code modified by LLM (iteration 5): updated to reflect helper fixes */
    /* code modified by LLM (iteration 4): fixed for loop to avoid ref patterns using index */
    let unique_blue = get_unique_blue_exec(&blue_cards);
    let mut max_net: i64 = 0;
    for i in 0..unique_blue.len()
    {
        let s = unique_blue[i];
        let blue_count = count_occurrences_exec(&blue_cards, s);
        let red_count = count_occurrences_exec(&red_cards, s);
        let net = blue_count as i64 - red_count as i64;
        if net > max_net
        {
            max_net = net;
        }
    }
    max_net as i8
}
// </vc-code>


}

fn main() {}