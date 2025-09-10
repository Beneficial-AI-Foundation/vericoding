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
lemma seq_min_tail(s: seq<int>)
    requires |s| > 1
    ensures seq_min(s) == if s[0] <= seq_min(s[1..]) then s[0] else seq_min(s[1..])
{
}

lemma seq_min_in_s(s: seq<int>, k: int)
    requires |s| > 0
    requires 0 <= k < |s| && s[k] == seq_min(s)
    ensures exists i :: 0 <= i < |s| && s[i] == seq_min(s)
{
}

lemma tail_contains_seq_min(s: seq<int>)
    requires |s| > 1
    requires seq_min(s) == seq_min(s[1..])
    ensures seq_min(s[1..]) in s[1..]
{
}

lemma head_is_seq_min(s: seq<int>)
    requires |s| > 1
    requires seq_min(s) == s[0]
    ensures s[0] <= seq_min(s[1..])
{
}

lemma min_value_exists(arr: seq<int>, min_val: int)
    requires ValidInput(arr)
    ensures exists i :: 0 <= i < |arr| && arr[i] == min_val
{
}

lemma consecutive_min_positions(arr: seq<int>, min_val: int)
    requires ValidInput(arr)
    ensures exists i, j :: 0 <= i < j < |arr| && arr[i] == arr[j] == min_val
{
}
// </vc-helpers>
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
    var first_occurrence := -1;
    var min_distance := |arr|;
    var i := 0;
    
    while i < |arr|
        invariant 0 <= i <= |arr|
        invariant first_occurrence >= -1 && first_occurrence < |arr|
        invariant first_occurrence >= 0 ==> arr[first_occurrence] == min_val
        invariant min_val == seq_min(arr)
        invariant forall k :: 0 <= k < i && arr[k] == min_val && first_occurrence >= 0 ==> exists j :: k < j < |arr| && arr[j] == min_val && j - k >= min_distance || min_distance == |arr|
    {
        if arr[i] == min_val {
            if first_occurrence == -1 {
                first_occurrence := i;
            } else {
                var distance := i - first_occurrence;
                if distance < min_distance {
                    min_distance := distance;
                }
                first_occurrence := i;
            }
        }
        i := i + 1;
    }
    
    result := min_distance;
}
// </vc-code>

