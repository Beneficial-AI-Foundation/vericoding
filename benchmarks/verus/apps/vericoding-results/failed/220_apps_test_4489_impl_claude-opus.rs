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
fn count_occurrences_exec(cards: &Vec<&str>, target: &str) -> (count: usize)
    ensures count as int == count_occurrences(cards@, target)
{
    let mut i: usize = 0;
    let mut count: usize = 0;
    while i < cards.len()
        invariant
            0 <= i <= cards.len(),
            count as int == count_occurrences(cards@.subrange(0, i as int), target)
    {
        if cards[i] == target {
            count = count + 1;
        }
        i = i + 1;
    }
    assert(cards@.subrange(0, cards.len() as int) == cards@);
    count
}

fn get_unique_strings_exec(all_strings: &Vec<&str>) -> (result: Vec<&str>)
    ensures result@ == get_unique_strings(all_strings@)
{
    let mut result = Vec::new();
    let mut i: usize = 0;
    while i < all_strings.len()
        invariant
            0 <= i <= all_strings.len(),
            result@ == get_unique_strings(all_strings@.subrange(0, i as int))
    {
        let s = all_strings[i];
        let mut found = false;
        let mut j: usize = 0;
        while j < result.len()
            invariant
                0 <= j <= result.len(),
                found <==> result@.subrange(0, j as int).contains(s)
        {
            if result[j] == s {
                found = true;
            }
            j = j + 1;
        }
        assert(result@.subrange(0, result.len() as int) == result@);
        if !found {
            result.push(s);
        }
        i = i + 1;
    }
    assert(all_strings@.subrange(0, all_strings.len() as int) == all_strings@);
    result
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
    let unique_blue = get_unique_strings_exec(&blue_cards);
    let mut max_earnings: i8 = 0;
    let mut i: usize = 0;
    
    while i < unique_blue.len()
        invariant
            0 <= i <= unique_blue.len(),
            max_earnings >= 0,
            max_earnings as int == max_net_earnings_helper(unique_blue@, blue_cards@, red_cards@, i as int, 0)
    {
        let s = unique_blue[i];
        let blue_count = count_occurrences_exec(&blue_cards, s) as i8;
        let red_count = count_occurrences_exec(&red_cards, s) as i8;
        let net = blue_count - red_count;
        if net > max_earnings {
            max_earnings = net;
        }
        i = i + 1;
    }
    
    max_earnings
}
// </vc-code>


}

fn main() {}