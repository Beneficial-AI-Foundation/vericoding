predicate ValidInput(n: int, heights: seq<int>)
{
    n > 0 && |heights| == n &&
    (forall i :: 0 <= i < n ==> heights[i] >= 0) &&
    (forall i :: 0 <= i < n-1 ==> heights[i] < heights[i+1])
}

predicate ValidOutput(n: int, result: seq<int>)
{
    |result| == n &&
    (forall i :: 0 <= i < n ==> result[i] >= 0) &&
    (forall i :: 0 <= i < n-1 ==> result[i] <= result[i+1]) &&
    (forall i :: 0 <= i < n-1 ==> result[i+1] - result[i] <= 1)
}

predicate IsStable(result: seq<int>)
{
    forall i :: 0 <= i < |result|-1 ==> !(result[i] + 2 <= result[i+1])
}

function sum_seq(s: seq<int>): int
{
    if |s| == 0 then 0 else s[0] + sum_seq(s[1..])
}

// <vc-helpers>
lemma sum_seq_append(s1: seq<int>, s2: seq<int>)
    ensures sum_seq(s1 + s2) == sum_seq(s1) + sum_seq(s2)
{
    if |s1| == 0 {
        assert s1 + s2 == s2;
        assert sum_seq(s1) == 0;
    } else {
        assert (s1 + s2)[0] == s1[0];
        assert (s1 + s2)[1..] == s1[1..] + s2;
        sum_seq_append(s1[1..], s2);
    }
}

lemma sum_seq_single(x: int)
    ensures sum_seq([x]) == x
{
}

lemma sum_seq_update_preserves_sum(s: seq<int>, i: int, old_val: int, new_val: int)
    requires 0 <= i < |s|
    requires s[i] == old_val
    ensures sum_seq(s[i := new_val]) == sum_seq(s) - old_val + new_val
{
    var s' := s[i := new_val];
    if i == 0 {
        if |s| == 1 {
            assert s' == [new_val];
        } else {
            assert s'[1..] == s[1..];
        }
    } else {
        sum_seq_update_preserves_sum(s[1..], i-1, old_val, new_val);
    }
}

function min(a: int, b: int): int
{
    if a <= b then a else b
}

lemma consecutive_diff_preserved(s: seq<int>, i: int, new_val: int)
    requires 0 <= i < |s|
    requires i > 0 ==> new_val >= s[i-1]
    requires i < |s|-1 ==> new_val <= s[i+1]
    requires i > 0 ==> new_val - s[i-1] <= 1
    requires i < |s|-1 ==> s[i+1] - new_val <= 1
    requires forall j :: 0 <= j < |s|-1 ==> s[j+1] - s[j] <= 1
    ensures forall j :: 0 <= j < |s|-1 ==> s[i := new_val][j+1] - s[i := new_val][j] <= 1
{
    var s' := s[i := new_val];
    forall j | 0 <= j < |s|-1
        ensures s'[j+1] - s'[j] <= 1
    {
        if j == i-1 && i > 0 {
            assert s'[j] == s[j] && s'[j+1] == new_val;
        } else if j == i && i < |s|-1 {
            assert s'[j] == new_val && s'[j+1] == s[j+1];
        } else {
            assert s'[j] == s[j] && s'[j+1] == s[j+1];
        }
    }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, heights: seq<int>) returns (result: seq<int>)
    requires ValidInput(n, heights)
    ensures ValidOutput(n, result)
    ensures sum_seq(result) == sum_seq(heights)
    ensures IsStable(result)
// </vc-spec>
// <vc-code>
{
    result := heights;
    var excess := 0;
    var i := 0;
    
    while i < n
        invariant 0 <= i <= n
        invariant |result| == n
        invariant forall j :: 0 <= j < n ==> result[j] >= 0
        invariant forall j :: 0 <= j < i-1 ==> result[j] <= result[j+1]
        invariant forall j :: 0 <= j < i-1 ==> result[j+1] - result[j] <= 1
        invariant forall j :: 0 <= j < i-1 ==> !(result[j] + 2 <= result[j+1])
        invariant sum_seq(result) + excess == sum_seq(heights)
        invariant excess >= 0
    {
        if i == 0 {
            var old_val := result[0];
            result := result[0 := result[0] + excess];
            excess := 0;
        } else {
            var max_allowed := result[i-1] + 1;
            if result[i] > max_allowed {
                var old_val := result[i];
                excess := excess + (result[i] - max_allowed);
                result := result[i := max_allowed];
            } else {
                var can_add := min(excess, max_allowed - result[i]);
                if can_add > 0 {
                    var old_val := result[i];
                    result := result[i := result[i] + can_add];
                    excess := excess - can_add;
                }
            }
        }
        i := i + 1;
    }
    
    // Distribute remaining excess to the last element
    if excess > 0 {
        var old_val := result[n-1];
        result := result[n-1 := result[n-1] + excess];
    }
    
    // Assert final properties
    assert forall j :: 0 <= j < n-1 ==> result[j] <= result[j+1];
    assert forall j :: 0 <= j < n-1 ==> result[j+1] - result[j] <= 1;
    assert forall j :: 0 <= j < n-1 ==> !(result[j] + 2 <= result[j+1]);
}
// </vc-code>

