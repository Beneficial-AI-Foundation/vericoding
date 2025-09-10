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
    var first_pos := 0;
    var last_pos := 0;
    var min_distance := |arr|;
    
    var i := 0;
    while i < |arr|
        invariant 0 <= i <= |arr|
        invariant first_pos >= 0 && last_pos >= 0
        invariant min_val == seq_min(arr)
    {
        if arr[i] == min_val {
            if first_pos == 0 && arr[0] != min_val {
                first_pos := i;
            }
            last_pos := i;
            
            if first_pos > 0 && last_pos > first_pos {
                var distance := last_pos - first_pos;
                if distance < min_distance {
                    min_distance := distance;
                }
                first_pos := last_pos;
            }
        }
        i := i + 1;
    }
    
    result := min_distance;
}
// </vc-code>

