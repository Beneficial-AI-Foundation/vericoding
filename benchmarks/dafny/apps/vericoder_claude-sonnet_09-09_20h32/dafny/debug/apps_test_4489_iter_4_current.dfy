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
lemma get_unique_strings_preserves_membership(all_strings: seq<string>, s: string)
    ensures s in all_strings ==> s in get_unique_strings(all_strings)
{
    if |all_strings| == 0 {
    } else {
        get_unique_strings_preserves_membership(all_strings[1..], s);
        if all_strings[0] == s {
            if all_strings[0] in get_unique_strings(all_strings[1..]) {
            } else {
            }
        } else {
            if all_strings[0] in get_unique_strings(all_strings[1..]) {
            } else {
            }
        }
    }
}

lemma count_occurrences_prefix_property(cards: seq<string>, target: string, i: int)
    requires 0 <= i <= |cards|
    ensures count_occurrences(cards[..i], target) + count_occurrences(cards[i..], target) == count_occurrences(cards, target)
{
    if i == 0 {
        assert cards[..i] == [];
        assert cards[i..] == cards;
    } else if i == |cards| {
        assert cards[..i] == cards;
        assert cards[i..] == [];
    } else {
        assert cards == cards[..i] + cards[i..];
        assert cards[..i] == cards[..(i-1)] + [cards[i-1]];
        count_occurrences_prefix_property(cards, target, i - 1);
        if cards[i-1] == target {
            assert count_occurrences(cards[..i], target) == count_occurrences(cards[..(i-1)], target) + 1;
        } else {
            assert count_occurrences(cards[..i], target) == count_occurrences(cards[..(i-1)], target);
        }
    }
}

lemma count_occurrences_slice_step(cards: seq<string>, target: string, i: int)
    requires 0 <= i < |cards|
    ensures count_occurrences(cards[..(i+1)], target) == 
            count_occurrences(cards[..i], target) + (if cards[i] == target then 1 else 0)
{
    if i == 0 {
        assert cards[..i] == [];
        assert cards[..(i+1)] == [cards[0]];
        if cards[i] == target {
            calc {
                count_occurrences(cards[..(i+1)], target);
                == count_occurrences([cards[0]], target);
                == 1 + count_occurrences([], target);
                == 1 + 0;
                == 1;
                == count_occurrences([], target) + 1;
                == count_occurrences(cards[..i], target) + 1;
            }
        } else {
            calc {
                count_occurrences(cards[..(i+1)], target);
                == count_occurrences([cards[0]], target);
                == count_occurrences([], target);
                == 0;
                == count_occurrences(cards[..i], target);
            }
        }
    } else {
        count_occurrences_slice_step(cards, target, i-1);
        assert cards[..(i+1)] == cards[..i] + [cards[i]];
        
        if cards[i] == target {
            calc {
                count_occurrences(cards[..(i+1)], target);
                == count_occurrences(cards[..i] + [cards[i]], target);
                == count_occurrences(cards[..i], target) + count_occurrences([cards[i]], target);
                == count_occurrences(cards[..i], target) + 1;
            }
        } else {
            calc {
                count_occurrences(cards[..(i+1)], target);
                == count_occurrences(cards[..i] + [cards[i]], target);
                == count_occurrences(cards[..i], target) + count_occurrences([cards[i]], target);
                == count_occurrences(cards[..i], target) + 0;
                == count_occurrences(cards[..i], target);
            }
        }
    }
}

lemma count_occurrences_append(s1: seq<string>, s2: seq<string>, target: string)
    ensures count_occurrences(s1 + s2, target) == count_occurrences(s1, target) + count_occurrences(s2, target)
{
    if |s1| == 0 {
        assert s1 + s2 == s2;
    } else {
        calc {
            count_occurrences(s1 + s2, target);
            == count_occurrences([s1[0]] + (s1[1..] + s2), target);
            == count_occurrences([s1[0]] + s1[1..] + s2, target);
        }
        count_occurrences_append(s1[1..], s2, target);
        if s1[0] == target {
            calc {
                count_occurrences(s1 + s2, target);
                == 1 + count_occurrences((s1[1..] + s2), target);
                == 1 + count_occurrences(s1[1..], target) + count_occurrences(s2, target);
                == (1 + count_occurrences(s1[1..], target)) + count_occurrences(s2, target);
                == count_occurrences(s1, target) + count_occurrences(s2, target);
            }
        } else {
            calc {
                count_occurrences(s1 + s2, target);
                == count_occurrences((s1[1..] + s2), target);
                == count_occurrences(s1[1..], target) + count_occurrences(s2, target);
                == count_occurrences(s1, target) + count_occurrences(s2, target);
            }
        }
    }
}

method get_unique_strings_impl(all_strings: seq<string>) returns (result: seq<string>)
    ensures result == get_unique_strings(all_strings)
{
    if |all_strings| == 0 {
        result := [];
    } else {
        var rest_unique := get_unique_strings_impl(all_strings[1..]);
        if all_strings[0] in rest_unique {
            result := rest_unique;
        } else {
            result := [all_strings[0]] + rest_unique;
        }
    }
}

method count_occurrences_impl(cards: seq<string>, target: string) returns (count: int)
    ensures count == count_occurrences(cards, target)
    ensures count >= 0
{
    count := 0;
    var i := 0;
    while i < |cards|
        invariant 0 <= i <= |cards|
        invariant count == count_occurrences(cards[..i], target)
        invariant count >= 0
    {
        count_occurrences_slice_step(cards, target, i);
        if cards[i] == target {
            count := count + 1;
        }
        i := i + 1;
    }
    assert cards[..i] == cards;
}

method max_net_earnings_helper_impl(unique_blue: seq<string>, blue_cards: seq<string>, red_cards: seq<string>, index: int, current_max: int) returns (result: int)
    requires 0 <= index <= |unique_blue|
    ensures result == max_net_earnings_helper(unique_blue, blue_cards, red_cards, index, current_max)
    ensures result >= current_max
    decreases |unique_blue| - index
{
    if index >= |unique_blue| {
        result := current_max;
    } else {
        var s := unique_blue[index];
        var blue_count := count_occurrences_impl(blue_cards, s);
        var red_count := count_occurrences_impl(red_cards, s);
        var net := blue_count - red_count;
        var new_max := if net > current_max then net else current_max;
        result := max_net_earnings_helper_impl(unique_blue, blue_cards, red_cards, index + 1, new_max);
    }
}
// </vc-helpers>

// <vc-spec>
method solve(blue_cards: seq<string>, red_cards: seq<string>) returns (result: int)
    ensures result >= 0
    ensures result == max_net_earnings(blue_cards, red_cards)
// </vc-spec>
// <vc-code>
{
    var unique_blue := get_unique_strings_impl(blue_cards);
    result := max_net_earnings_helper_impl(unique_blue, blue_cards, red_cards, 0, 0);
}
// </vc-code>

