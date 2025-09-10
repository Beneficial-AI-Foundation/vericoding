function seq_min(s: seq<int>): int
    requires |s| > 0
    ensures seq_min(s) in s
    ensures forall k :: 0 <= k < |s| ==> seq_min(s) <= s[k]
{
    if |s| == 1 then s[0]
    else if s[0] <= seq_min(s[1..]) then s[0]
    else seq_min(s[1..])
}

predicate ValidInput(arr: seq<int>)
{
    |arr| >= 2 && 
    exists i, j :: 0 <= i < j < |arr| && arr[i] == arr[j] == seq_min(arr)
}

// <vc-helpers>
lemma MinDistanceExists(arr: seq<int>)
    requires ValidInput(arr)
    ensures exists d :: d > 0 && d <= |arr| - 1 && 
            (exists i, j :: 0 <= i < j < |arr| && arr[i] == arr[j] == seq_min(arr) && j - i == d) &&
            (forall i, j :: 0 <= i < j < |arr| && arr[i] == arr[j] == seq_min(arr) ==> j - i >= d)
{
    var min_val := seq_min(arr);
    var pairs := set i, j | 0 <= i < j < |arr| && arr[i] == arr[j] == min_val :: j - i;
    assert pairs != {};
    var d := MinInSet(pairs);
    assert d in pairs;
    assert d > 0;
    assert d <= |arr| - 1;
}

function MinInSet(s: set<int>): int
    requires s != {} && forall x :: x in s ==> x > 0
    ensures MinInSet(s) in s
    ensures forall x :: x in s ==> MinInSet(s) <= x
{
    var x :| x in s;
    if s == {x} then x
    else if x <= MinInSet(s - {x}) then x
    else MinInSet(s - {x})
}
// </vc-helpers>

// <vc-spec>
method solve(arr: seq<int>) returns (result: int)
    requires ValidInput(arr)
    ensures result > 0
    ensures result <= |arr| - 1
    ensures exists i, j :: 0 <= i < j < |arr| && arr[i] == arr[j] == seq_min(arr) && j - i == result
    ensures forall i, j :: 0 <= i < j < |arr| && arr[i] == arr[j] == seq_min(arr) ==> j - i >= result
// </vc-spec>
// <vc-code>
{
    var min_val := seq_min(arr);
    var min_distance := |arr|;
    var last_min_pos := -1;
    
    for i := 0 to |arr|
        invariant 0 <= i <= |arr|
        invariant last_min_pos >= -1
        invariant last_min_pos < i
        invariant last_min_pos >= 0 ==> arr[last_min_pos] == min_val
        invariant min_distance <= |arr|
        invariant last_min_pos >= 0 ==> min_distance < |arr|
        invariant min_distance < |arr| ==> exists p, q :: 0 <= p < q < i && arr[p] == arr[q] == min_val && q - p == min_distance
        invariant forall p, q :: 0 <= p < q < i && arr[p] == arr[q] == min_val ==> q - p >= min_distance
    {
        if arr[i] == min_val {
            if last_min_pos >= 0 {
                var distance := i - last_min_pos;
                if distance < min_distance {
                    min_distance := distance;
                }
            }
            last_min_pos := i;
        }
    }
    
    result := min_distance;
}
// </vc-code>

