// <vc-preamble>
function minimum_replacements_for_zigzag(v: seq<int>): int
    requires |v| >= 2 && |v| % 2 == 0
    requires forall i :: 0 <= i < |v| ==> 1 <= v[i] <= 100000
{
    var odd_positions := |v| / 2;
    var even_positions := |v| / 2;
    var max_odd_freq := max_frequency_at_odd_positions(v);
    var max_even_freq := max_frequency_at_even_positions(v);
    var best_odd_value := best_value_for_odd_positions(v);
    var best_even_value := best_value_for_even_positions(v);

    if best_odd_value != best_even_value then
        odd_positions + even_positions - max_odd_freq - max_even_freq
    else
        var second_max_odd := second_max_frequency_at_odd_positions(v, best_odd_value);
        var second_max_even := second_max_frequency_at_even_positions(v, best_even_value);
        var option1 := odd_positions + even_positions - max_odd_freq - second_max_even;
        var option2 := odd_positions + even_positions - second_max_odd - max_even_freq;
        if option1 <= option2 then option1 else option2
}
// </vc-preamble>

// <vc-helpers>
function max_frequency_at_odd_positions(v: seq<int>): int
    requires |v| >= 2
    requires forall i :: 0 <= i < |v| ==> 1 <= v[i] <= 100000
{
    max_element_in_range(1, 100000, value => count_at_odd_positions(v, value))
}

function max_frequency_at_even_positions(v: seq<int>): int
    requires |v| >= 2
    requires forall i :: 0 <= i < |v| ==> 1 <= v[i] <= 100000
{
    max_element_in_range(1, 100000, value => count_at_even_positions(v, value))
}

function best_value_for_odd_positions(v: seq<int>): int
    requires |v| >= 2
    requires forall i :: 0 <= i < |v| ==> 1 <= v[i] <= 100000
    ensures 1 <= best_value_for_odd_positions(v) <= 100000
    ensures count_at_odd_positions(v, best_value_for_odd_positions(v)) == max_frequency_at_odd_positions(v)
{
    first_value_with_max_freq(1, 100000, value => count_at_odd_positions(v, value), max_frequency_at_odd_positions(v))
}

function best_value_for_even_positions(v: seq<int>): int
    requires |v| >= 2
    requires forall i :: 0 <= i < |v| ==> 1 <= v[i] <= 100000
    ensures 1 <= best_value_for_even_positions(v) <= 100000
    ensures count_at_even_positions(v, best_value_for_even_positions(v)) == max_frequency_at_even_positions(v)
{
    first_value_with_max_freq(1, 100000, value => count_at_even_positions(v, value), max_frequency_at_even_positions(v))
}

function second_max_frequency_at_odd_positions(v: seq<int>, exclude: int): int
    requires |v| >= 2
    requires forall i :: 0 <= i < |v| ==> 1 <= v[i] <= 100000
    requires 1 <= exclude <= 100000
{
    max_element_in_range(1, 100000, value => if value == exclude then 0 else count_at_odd_positions(v, value))
}

function second_max_frequency_at_even_positions(v: seq<int>, exclude: int): int
    requires |v| >= 2
    requires forall i :: 0 <= i < |v| ==> 1 <= v[i] <= 100000
    requires 1 <= exclude <= 100000
{
    max_element_in_range(1, 100000, value => if value == exclude then 0 else count_at_even_positions(v, value))
}

function count_at_odd_positions(v: seq<int>, value: int): int
    requires forall i :: 0 <= i < |v| ==> 1 <= v[i] <= 100000
{
    |set j | 0 <= j < |v| && j % 2 == 1 && v[j] == value|
}

function count_at_even_positions(v: seq<int>, value: int): int
    requires forall i :: 0 <= i < |v| ==> 1 <= v[i] <= 100000
{
    |set j | 0 <= j < |v| && j % 2 == 0 && v[j] == value|
}

function max_element_in_range(start: int, end: int, f: int -> int): int
    requires start <= end
    decreases end - start
{
    if start == end then f(start)
    else
        var mid := (start + end) / 2;
        var left_max := max_element_in_range(start, mid, f);
        var right_max := max_element_in_range(mid + 1, end, f);
        if left_max >= right_max then left_max else right_max
}

function first_value_with_max_freq(start: int, end: int, f: int -> int, target_freq: int): int
    requires start <= end
    requires exists i :: start <= i <= end && f(i) == target_freq
    decreases end - start
{
    if start == end then start
    else if f(start) == target_freq then start
    else first_value_with_max_freq(start + 1, end, f, target_freq)
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, v: seq<int>) returns (result: int)
    requires n >= 2 && n % 2 == 0
    requires |v| == n
    requires forall i :: 0 <= i < |v| ==> 1 <= v[i] <= 100000
    ensures 0 <= result <= n
    ensures result == minimum_replacements_for_zigzag(v)
// </vc-spec>
// <vc-code>
{
    var odd_counts := new int[100001];
    var even_counts := new int[100001];

    var i := 0;
    while i < n
        invariant 0 <= i <= n
    {
        if i % 2 == 0 {
            even_counts[v[i]] := even_counts[v[i]] + 1;
        } else {
            odd_counts[v[i]] := odd_counts[v[i]] + 1;
        }
        i := i + 1;
    }

    var max_odd := 0;
    var max_odd_val := 1;
    var max_even := 0;
    var max_even_val := 1;

    i := 1;
    while i <= 100000
        invariant 1 <= i <= 100001
        invariant 0 <= max_odd <= n / 2
        invariant 0 <= max_even <= n / 2
        invariant 1 <= max_odd_val <= 100000
        invariant 1 <= max_even_val <= 100000
    {
        if odd_counts[i] > max_odd {
            max_odd := odd_counts[i];
            max_odd_val := i;
        }
        if even_counts[i] > max_even {
            max_even := even_counts[i];
            max_even_val := i;
        }
        i := i + 1;
    }

    var sum_odd := n / 2;
    var sum_even := n / 2;

    assert max_odd <= sum_odd;
    assert max_even <= sum_even;

    if max_odd_val != max_even_val {
        result := sum_odd + sum_even - max_even - max_odd;
        assert result >= 0;
        assert result <= n;
    } else {
        var second_max_odd := 0;
        var second_max_even := 0;

        i := 1;
        while i <= 100000
            invariant 1 <= i <= 100001
            invariant 0 <= second_max_odd <= n / 2
            invariant 0 <= second_max_even <= n / 2
        {
            if i != max_odd_val {
                if odd_counts[i] > second_max_odd {
                    second_max_odd := odd_counts[i];
                }
                if even_counts[i] > second_max_even {
                    second_max_even := even_counts[i];
                }
            }
            i := i + 1;
        }

        assert second_max_odd <= sum_odd;
        assert second_max_even <= sum_even;

        if max_odd - second_max_odd > max_even - second_max_even {
            result := sum_odd + sum_even - max_odd - second_max_even;
        } else {
            result := sum_odd + sum_even - second_max_odd - max_even;
        }
        assert result >= 0;
        assert result <= n;
    }
}
// </vc-code>
