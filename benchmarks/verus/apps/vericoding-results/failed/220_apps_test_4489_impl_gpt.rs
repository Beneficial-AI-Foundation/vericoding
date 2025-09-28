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
proof fn blue_prefix_has_string(blue: Seq<&str>, idx: int, s: &str) 
    requires
        0 <= idx <= blue.len(),
    ensures
        (exists|j: int| 0 <= j < idx && blue[j] == s) ==> blue.subrange(0, idx).contains(s),
{
}

fn contains_in_prefix(vec: &Vec<&str>, idx: usize, s: &str) -> (b: bool)
    requires
        idx <= vec.len(),
    ensures
        b == vec@.subrange(0, idx as int).contains(s),
{
    let mut i: usize = 0;
    let mut found: bool = false;
    while i < idx
        invariant
            i <= idx,
            found == vec@.subrange(0, i as int).contains(s),
        decreases idx - i
    {
        if vec[i] == s {
            found = true;
        }
        i = i + 1;
    }
    found
}

fn count_occurrences_exec(cards: &Vec<&str>, target: &str) -> (r: usize)
    ensures
        r as int == count_occurrences(cards@, target),
{
    let n = cards.len();
    let mut i: usize = 0;
    let mut c: usize = 0;
    while i < n
        invariant
            i <= n,
            c as int == count_occurrences(cards@.subrange(0, i as int), target),
        decreases n - i
    {
        if cards[i] == target {
            c = c + 1;
        }
        i = i + 1;
    }
    c
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
    let n_blue = blue_cards.len();
    let n_red = red_cards.len();

    // Build unique strings from blue_cards in order of first appearance
    let mut uniques: Vec<&str> = Vec::new();
    let mut i: usize = 0;
    while i < n_blue
        invariant
            i <= n_blue,
            // uniques contains exactly first occurrences among processed prefix
            forall|k: int|
                0 <= k < i as int && (
                    (exists|j: int| 0 <= j < k && blue_cards@[j] == blue_cards@[k]) ==> !uniques@.contains(blue_cards@[k])
                ),
        decreases n_blue - i
    {
        let s = blue_cards[i];
        let already = contains_in_prefix(&blue_cards, i, s);
        if !already {
            uniques.push(s);
        }
        i = i + 1;
    }

    // Compute maximum net earnings across unique blue strings
    let mut max_net_i128: i128 = 0;
    let mut u: usize = 0;
    while u < uniques.len()
        invariant
            u <= uniques.len(),
            max_net_i128 >= 0,
        decreases uniques.len() - u
    {
        let s = uniques[u];
        let blue_c = count_occurrences_exec(&blue_cards, s) as i128;
        let red_c = count_occurrences_exec(&red_cards, s) as i128;
        let net = blue_c - red_c;
        if net > max_net_i128 { max_net_i128 = net; }
        u = u + 1;
    }

    // Cast to i8 for the result
    let result_i8: i8 = max_net_i128 as i8;
    result_i8
}
// </vc-code>


}

fn main() {}