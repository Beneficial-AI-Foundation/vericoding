predicate ValidInput(n: int, m: int, k: int, emotes: seq<int>)
{
    n >= 2 && k >= 1 && m >= 1 && |emotes| == n &&
    forall i :: 0 <= i < |emotes| ==> emotes[i] >= 1
}

function MaxHappiness(n: int, m: int, k: int, emotes: seq<int>): int
    requires ValidInput(n, m, k, emotes)
{
    var k_plus_1 := k + 1;
    var total := m / k_plus_1;
    var remainder := m % k_plus_1;
    // Assumes optimal strategy using highest and second highest values
    var max_val := MaxValue(emotes);
    var second_max_val := SecondMaxValue(emotes);
    remainder * max_val + max_val * (total * k) + second_max_val * total
}

function MaxValue(s: seq<int>): int
    requires |s| >= 1
    requires forall i :: 0 <= i < |s| ==> s[i] >= 1
    ensures MaxValue(s) >= 1
    ensures exists i :: 0 <= i < |s| && s[i] == MaxValue(s)
{
    if |s| == 1 then s[0]
    else if s[0] >= MaxValue(s[1..]) then s[0]
    else MaxValue(s[1..])
}

function SecondMaxValue(s: seq<int>): int
    requires |s| >= 2
    requires forall i :: 0 <= i < |s| ==> s[i] >= 1
{
    var max_val := MaxValue(s);
    var filtered := FilterOut(s, max_val, 1);
    if |filtered| > 0 then MaxValue(filtered) else 1
}

function FilterOut(s: seq<int>, val: int, count: int): seq<int>
    requires count >= 0
    requires forall i :: 0 <= i < |s| ==> s[i] >= 1
    ensures forall i :: 0 <= i < |FilterOut(s, val, count)| ==> FilterOut(s, val, count)[i] >= 1
{
    if |s| == 0 || count == 0 then s
    else if s[0] == val then FilterOut(s[1..], val, count - 1)
    else [s[0]] + FilterOut(s[1..], val, count)
}

// <vc-helpers>
function MaxValueIndex(s: seq<int>): int
    requires |s| >= 1
    requires forall i :: 0 <= i < |s| ==> s[i] >= 1
    ensures 0 <= MaxValueIndex(s) < |s|
    ensures s[MaxValueIndex(s)] == MaxValue(s)
{
    if |s| == 1 then 0
    else var res_rest := MaxValueIndex(s[1..]);
         if s[0] >= s[res_rest + 1] then 0
         else res_rest + 1
}

function SortedSeq(s: seq<int>): seq<int>
    requires forall i :: 0 <= i < |s| ==> s[i] >= 1
    ensures |SortedSeq(s)| == |s|
    ensures forall i :: 0 <= i < |SortedSeq(s)| ==> SortedSeq(s)[i] >= 1
    ensures forall i, j :: 0 <= i < j < |SortedSeq(s)| ==> SortedSeq(s)[i] >= SortedSeq(s)[j]
    decreases |s|
{
    if |s| <= 1 then s
    else
        var max_val_index := MaxValueIndex(s);
        var max_val := s[max_val_index];
        var temp_s := s;
        var rest_seq := temp_s[..max_val_index] + temp_s[max_val_index+1 ..];
        [max_val] + SortedSeq(rest_seq)
}

function GetNthLargest(s: seq<int>, n: int): int
    requires |s| >= n
    requires n >= 1
    requires forall i :: 0 <= i < |s| ==> s[i] >= 1
    ensures GetNthLargest(s, n) >= 1
{
    SortedSeq(s)[n-1]
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, k: int, emotes: seq<int>) returns (result: int)
    requires ValidInput(n, m, k, emotes)
    ensures result >= 0
// </vc-spec>
// <vc-code>
{
    var k_plus_1 := k + 1;
    var total_blocks := m / k_plus_1;
    var remainder_clicks := m % k_plus_1;

    var sorted_emotes := SortedSeq(emotes);
    var max_val := sorted_emotes[0];
    var second_max_val := sorted_emotes[1];

    var result_val := remainder_clicks * max_val + (total_blocks * k) * max_val + total_blocks * second_max_val;
    return result_val;
}
// </vc-code>

