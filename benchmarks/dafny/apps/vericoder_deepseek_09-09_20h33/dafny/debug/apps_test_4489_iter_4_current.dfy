function count_occurrences(cards: seq<string>, target: string): int
    ensures count_occurrences(cards, target) >= 0
{
    if |cards| == 0 then 0
    else if cards[0] == target then 1 + count_occurrences(cards[1..], target)
    else count_occurrences(cards[1..], target)
}

function get_unique_strings(all_strings: seq<string>): seq<string>
{
    if |all_strings| == 0 then []
    else 
        var rest_unique := get_unique_strings(all_strings[1..]);
        if all_strings[0] in rest_unique then rest_unique
        else [all_strings[0]] + rest_unique
}

function max_net_earnings(blue_cards: seq<string>, red_cards: seq<string>): int
    ensures max_net_earnings(blue_cards, red_cards) >= 0
{
    var unique_blue := get_unique_strings(blue_cards);
    max_net_earnings_helper(unique_blue, blue_cards, red_cards, 0, 0)
}

function max_net_earnings_helper(unique_blue: seq<string>, blue_cards: seq<string>, red_cards: seq<string>, index: int, current_max: int): int
    requires 0 <= index <= |unique_blue|
    ensures max_net_earnings_helper(unique_blue, blue_cards, red_cards, index, current_max) >= current_max
    decreases |unique_blue| - index
{
    if index >= |unique_blue| then current_max
    else
        var s := unique_blue[index];
        var blue_count := count_occurrences(blue_cards, s);
        var red_count := count_occurrences(red_cards, s);
        var net := blue_count - red_count;
        var new_max := if net > current_max then net else current_max;
        max_net_earnings_helper(unique_blue, blue_cards, red_cards, index + 1, new_max)
}

// <vc-helpers>
lemma max_net_earnings_positive(blue_cards: seq<string>, red_cards: seq<string>)
    ensures max_net_earnings(blue_cards, red_cards) >= 0
{
}

lemma max_net_earnings_helper_non_decreasing(unique_blue: seq<string>, blue_cards: seq<string>, red_cards: seq<string>, index: int, current_max: int)
    requires 0 <= index <= |unique_blue|
    requires current_max >= 0
    ensures max_net_earnings_helper(unique_blue, blue_cards, red_cards, index, current_max) >= current_max
{
}

lemma max_net_earnings_helper_recursive(unique_blue: seq<string>, blue_cards: seq<string>, red_cards: seq<string>, i: int, curr_max: int, new_max: int)
    requires 0 <= i < |unique_blue|
    requires curr_max >= 0
    ensures max_net_earnings_helper(unique_blue, blue_cards, red_cards, i, curr_max) == 
            max_net_earnings_helper(unique_blue, blue_cards, red_cards, i + 1, 
                if count_occurrences(blue_cards, unique_blue[i]) - count_occurrences(red_cards, unique_blue[i]) > curr_max 
                then count_occurrences(blue_cards, unique_blue[i]) - count_occurrences(red_cards, unique_blue[i]) 
                else curr_max)
{
    // The functional implementation provides the recursive behavior
    // This lemma connects the recursive calls
}
// </vc-helpers>

// <vc-spec>
method solve(blue_cards: seq<string>, red_cards: seq<string>) returns (result: int)
    ensures result >= 0
    ensures result == max_net_earnings(blue_cards, red_cards)
// </vc-spec>
// <vc-code>
{
    var unique_blue := get_unique_strings(blue_cards);
    result := 0;
    var i := 0;
    while i < |unique_blue|
        invariant 0 <= i <= |unique_blue|
        invariant result >= 0
        invariant result == max_net_earnings_helper(unique_blue, blue_cards, red_cards, i, 0)
    {
        var s := unique_blue[i];
        var blue_count := count_occurrences(blue_cards, s);
        var red_count := count_occurrences(red_cards, s);
        var net := blue_count - red_count;
        var new_max := if net > result then net else result;
        max_net_earnings_helper_recursive(unique_blue, blue_cards, red_cards, i, result, new_max);
        result := new_max;
        i := i + 1;
    }
}
// </vc-code>

