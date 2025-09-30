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
lemma max_excluding_property(s: seq<int>, exclude_idx: int)
    requires 0 <= exclude_idx < |s|
    requires |s| >= 2
    ensures max_excluding(s, exclude_idx) == max_of_seq(s[..exclude_idx] + s[exclude_idx+1..])
{
    // Definition of max_excluding
}

lemma sequence_concat_property(s: seq<int>, i: int)
    requires 0 <= i < |s|
    ensures s[..i] + s[i+1..] == s[..i] + s[i+1..]
    ensures |s[..i] + s[i+1..]| == |s| - 1
{
    // Trivial by definition
}
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
    var i := 0;
    
    while i < |input|
        invariant 0 <= i <= |input|
        invariant |result| == i
        invariant forall j :: 0 <= j < i ==> result[j] == max_excluding(input, j)
    {
        var max_val := max_excluding(input, i);
        result := result + [max_val];
        i := i + 1;
    }
}
// </vc-code>

