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
proof fn max_net_earnings_helper_monotonic(unique_blue: Seq<&str>, blue_cards: Seq<&str>, red_cards: Seq<&str>, index: int, current_max: int, new_max2: int)
    requires 
        0 <= index <= unique_blue.len(),
        current_max >= 0,
        new_max2 >= current_max
    ensures max_net_earnings_helper(unique_blue, blue_cards, red_cards, index, current_max) <= max_net_earnings_helper(unique_blue, blue_cards, red_cards, index, new_max2)
    decreases unique_blue.len() - index
{
    if index >= unique_blue.len() {
    } else {
        let s = unique_blue[index];
        let blue_count = count_occurrences(blue_cards, s);
        let red_count = count_occurrences(red_cards, s);
        let net = blue_count - red_count;
        let actual_new_max = if net > current_max { net } else { current_max };
        let actual_new_max2 = if net > new_max2 { net } else { new_max2 };
        max_net_earnings_helper_monotonic(unique_blue, blue_cards, red_cards, index + 1, actual_new_max, actual_new_max2);
    }
}

fn string_eq(a: &str, b: &str) -> (res: bool)
    ensures res <==> a == b
{
    /* helper modified by LLM (iteration 5): fixed sequence to vector access for string comparison */
    if a.len() != b.len() {
        false
    } else {
        let a_bytes = a.as_bytes();
        let b_bytes = b.as_bytes();
        let mut i = 0;
        while i < a.len()
            invariant
                0 <= i <= a.len(),
                forall|j: int| 0 <= j < i ==> a_bytes[j] == b_bytes[j]
        {
            if a_bytes[i] != b_bytes[i] {
                return false;
            }
            i += 1;
        }
        true
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
{
    /* code modified by LLM (iteration 5): fixed implementation using vector indexing instead of sequence indexing */
    let mut result: i8 = 0;
    let mut seen: Set<&str> = set![];
    
    for i in 0..blue_cards.len() {
        let card = blue_cards[i];
        if !seen.contains(card) {
            seen = seen.insert(card);
            let mut blue_count: i8 = 0;
            let mut red_count: i8 = 0;
            
            proof {
                count_occurrences_non_negative(blue_cards@, card);
                count_occurrences_non_negative(red_cards@, card);
            }
            
            for j in 0..blue_cards.len() {
                if string_eq(blue_cards[j], card) {
                    blue_count += 1;
                }
            }
            
            for k in 0..red_cards.len() {
                if string_eq(red_cards[k], card) {
                    red_count += 1;
                }
            }
            
            let net_earning = blue_count - red_count;
            if net_earning > result {
                result = net_earning;
            }
        }
    }
    
    result
}
// </vc-code>


}

fn main() {}