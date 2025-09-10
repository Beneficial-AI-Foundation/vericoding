function max_of_seq(s: seq<int>): int
    requires |s| >= 1
    ensures forall i :: 0 <= i < |s| ==> s[i] <= max_of_seq(s)
    ensures exists i :: 0 <= i < |s| && s[i] == max_of_seq(s)
{
    if |s| == 1 then s[0]
    else if s[0] >= max_of_seq(s[1..]) then s[0]
    else max_of_seq(s[1..])
}

function max_excluding(s: seq<int>, exclude_idx: int): int
    requires 0 <= exclude_idx < |s|
    requires |s| >= 2
{
    var others := s[..exclude_idx] + s[exclude_idx+1..];
    max_of_seq(others)
}

// <vc-helpers>
lemma max_of_seq_properties(s: seq<int>)
    requires |s| >= 1
    ensures forall i :: 0 <= i < |s| ==> s[i] <= max_of_seq(s)
    ensures exists i :: 0 <= i < |s| && s[i] == max_of_seq(s)
{
}

lemma max_excluding_properties(s: seq<int>, exclude_idx: int)
    requires 0 <= exclude_idx < |s|
    requires |s| >= 2
    ensures max_excluding(s, exclude_idx) == max_of_seq(s[..exclude_idx] + s[exclude_idx+1..])
{
}

lemma max_of_seq_append(a: seq<int>, b: seq<int>)
    requires |a| >= 0 && |b| >= 0 && |a| + |b| >= 1
    ensures max_of_seq(a + b) == if |a| == 0 then max_of_seq(b)
        else if |b| == 0 then max_of_seq(a)
        else if max_of_seq(a) >= max_of_seq(b) then max_of_seq(a) else max_of_seq(b)
{
    if |a| == 0 {
        assert a + b == b;
    } else if |b| == 0 {
        assert a + b == a;
    } else {
        var max_a := max_of_seq(a);
        var max_b := max_of_seq(b);
        var max_ab := if max_a >= max_b then max_a else max_b;
        var combined := a + b;
        
        // max_combined >= max_ab
        max_of_seq_properties(combined);
        assert max_a <= max_of_seq(combined);
        assert max_b <= max_of_seq(combined);
        assert max_ab <= max_of_seq(combined);
        
        // max_combined <= max_ab
        max_of_seq_properties(a);
        max_of_seq_properties(b);
        if max_a >= max_b {
            assert forall x :: x in a ==> x <= max_a;
            assert forall x :: x in b ==> x <= max_b <= max_a;
            assert forall x :: x in combined ==> x <= max_a;
            assert max_of_seq(combined) <= max_a;
        } else {
            assert forall x :: x in a ==> x <= max_a <= max_b;
            assert forall x :: x in b ==> x <= max_b;
            assert forall x :: x in combined ==> x <= max_b;
            assert max_of_seq(combined) <= max_b;
        }
    }
}

lemma max_excluding_lemma(s: seq<int>, idx: int)
    requires 0 <= idx < |s|
    requires |s| >= 2
    ensures max_excluding(s, idx) == if s[idx] == max_of_seq(s) then
        (if |s| == 2 then s[1 - idx]
         else if idx == 0 then max_of_seq(s[1..])
         else if idx == |s| - 1 then max_of_seq(s[..|s|-1])
         else if max_of_seq(s[..idx]) >= max_of_seq(s[idx+1..]) then max_of_seq(s[..idx]) else max_of_seq(s[idx+1..]))
        else max_of_seq(s)
{
    var others := s[..idx] + s[idx+1..];
    assert max_excluding(s, idx) == max_of_seq(others);
    
    if s[idx] == max_of_seq(s) {
        if |s| == 2 {
            if idx == 0 {
                assert others == [s[1]];
                assert max_of_seq(others) == s[1];
            } else {
                assert others == [s[0]];
                assert max_of_seq(others) == s[0];
            }
        } else if idx == 0 {
            assert others == s[1..];
        } else if idx == |s| - 1 {
            assert others == s[..|s|-1];
        } else {
            max_of_seq_append(s[..idx], s[idx+1..]);
        }
    } else {
        max_of_seq_properties(s);
        assert exists i :: 0 <= i < |s| && s[i] == max_of_seq(s);
        assert max_of_seq(s) in others;
        max_of_seq_properties(others);
        assert max_of_seq(others) == max_of_seq(s);
    }
}

ghost function max_seq_if_removed(s: seq<int>, idx: int, current_max: int): int
    requires 0 <= idx < |s|
    requires current_max == max_of_seq(s)
{
    if s[idx] == current_max then
        if |s| == 1 then 0
        else if idx == 0 then max_of_seq(s[1..])
        else if idx == |s| - 1 then max_of_seq(s[..|s|-1])
        else if max_of_seq(s[..idx]) >= max_of_seq(s[idx+1..]) then max_of_seq(s[..idx]) else max_of_seq(s[idx+1..])
    else
        current_max
}

function count(s: seq<int>, val: int): int
{
    if |s| == 0 then 0
    else (if s[0] == val then 1 else 0) + count(s[1..], val)
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(input: seq<int>) returns (result: seq<int>)
    requires |input| >= 2
    ensures |result| == |input|
    ensures forall i :: 0 <= i < |input| ==> result[i] == max_excluding(input, i)
// </vc-spec>
// <vc-code>
{
    result := [];
    var n := |input|;
    var max_val := max_of_seq(input);
    var find_second_max := false;
    var max_count := 0;
    var second_max := 0;
    
    // Count occurrences of max_val and find second maximum if needed
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant max_count >= 0
        invariant max_count == count(input[..i], max_val)
        invariant forall j :: 0 <= j < i && input[j] < max_val ==> second_max >= input[j]
        invariant if find_second_max then exists k :: 0 <= k < i && input[k] < max_val && input[k] == second_max
                 else second_max == 0
    {
        if input[i] == max_val {
            max_count := max_count + 1;
        } else if !find_second_max || input[i] > second_max {
            second_max := input[i];
            find_second_max := true;
        }
        i := i + 1;
    }
    
    // Build result
    var j := 0;
    while j < n
        invariant 0 <= j <= n
        invariant |result| == j
        invariant forall k :: 0 <= k < j ==> result[k] == max_excluding(input, k)
    {
        max_excluding_lemma(input, j);
        if input[j] != max_val {
            result := result + [max_val];
        } else if max_count > 1 {
            result := result + [max_val];
        } else {
            assert find_second_max;
            result := result + [second_max];
        }
        j := j + 1;
    }
}
// </vc-code>

