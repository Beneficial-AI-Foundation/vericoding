function count_occurrences(s: seq<nat>, value: nat): nat
{
    if |s| == 0 then 0
    else if s[0] == value then 1 + count_occurrences(s[1..], value)
    else count_occurrences(s[1..], value)
}

function sum_seq(s: seq<nat>): nat
{
    if |s| == 0 then 0
    else s[0] + sum_seq(s[1..])
}

predicate subarray_matches_desired(subarray: seq<nat>, desired: seq<nat>, m: nat)
    requires |desired| == m
{
    forall color :: 1 <= color <= m ==> count_occurrences(subarray, color) == desired[color-1]
}

predicate ValidInput(n: nat, m: nat, colors: seq<nat>, desired: seq<nat>)
{
    |colors| == n &&
    |desired| == m &&
    (forall i :: 0 <= i < |colors| ==> 1 <= colors[i] <= m) &&
    (forall i :: 0 <= i < |desired| ==> desired[i] >= 0) &&
    sum_seq(desired) <= n
}

// <vc-helpers>
lemma count_occurrences_split(s: seq<nat>, value: nat, split: nat)
    requires 0 <= split <= |s|
    ensures count_occurrences(s, value) == count_occurrences(s[..split], value) + count_occurrences(s[split..], value)
{
    if split == 0 {
        assert s[..split] == [];
        assert s[split..] == s;
        calc {
            count_occurrences(s, value);
            == { assert s[..split] == []; }
            count_occurrences([] + s, value);
            == { assert count_occurrences([], value) == 0; }
            count_occurrences([], value) + count_occurrences(s, value);
        }
    } else if split == |s| {
        assert s[..split] == s;
        assert s[split..] == [];
        calc {
            count_occurrences(s, value);
            == { assert s[split..] == []; }
            count_occurrences(s + [], value);
            == { assert count_occurrences([], value) == 0; }
            count_occurrences(s, value) + count_occurrences([], value);
        }
    } else {
        calc {
            count_occurrences(s, value);
            == { assert s[..split] + s[split..] == s; }
            count_occurrences(s[..split] + s[split..], value);
            == { assert count_occurrences(s[..split] + s[split..], value) == count_occurrences(s[..split], value) + count_occurrences(s[split..], value); }
            count_occurrences(s[..split], value) + count_occurrences(s[split..], value);
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: nat, m: nat, colors: seq<nat>, desired: seq<nat>) returns (result: string)
    requires ValidInput(n, m, colors, desired)
    ensures result == "YES" <==> exists i, j :: 0 <= i <= j < n && subarray_matches_desired(colors[i..j+1], desired, m)
    ensures result == "YES" || result == "NO"
// </vc-spec>
// <vc-code>
{
    var left := 0;
    var right := 0;
    var window := colors[0..0];
    var current_counts := new nat[m];
    var desired_sum := sum_seq(desired);
    
    while right < n
        invariant 0 <= left <= right <= n
        invariant window == colors[left..right]
        invariant forall k :: 0 <= k < m ==> current_counts[k] == count_occurrences(window, k+1)
        invariant sum_seq(current_counts[..]) == |window|
    {
        window := window + [colors[right]];
        current_counts[colors[right]-1] := current_counts[colors[right]-1] + 1;
        right := right + 1;
        
        while sum_seq(current_counts[..]) > desired_sum && left < right
            invariant 0 <= left <= right <= n
            invariant window == colors[left..right]
            invariant forall k :: 0 <= k < m ==> current_counts[k] == count_occurrences(window, k+1)
            invariant sum_seq(current_counts[..]) == |window|
        {
            window := window[1..];
            current_counts[colors[left]-1] := current_counts[colors[left]-1] - 1;
            left := left + 1;
        }
        
        if sum_seq(current_counts[..]) == desired_sum {
            var matches := true;
            var k := 0;
            while k < m && matches
                invariant 0 <= k <= m
                invariant matches ==> forall j :: 0 <= j < k ==> current_counts[j] == desired[j]
            {
                if current_counts[k] != desired[k] {
                    matches := false;
                }
                k := k + 1;
            }
            if matches {
                return "YES";
            }
        }
    }
    
    return "NO";
}
// </vc-code>

