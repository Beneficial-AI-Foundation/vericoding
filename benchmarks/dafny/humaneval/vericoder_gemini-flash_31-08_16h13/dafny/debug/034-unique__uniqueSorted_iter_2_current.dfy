

// <vc-helpers>
function method multiset<T>(s: seq<T>): multiset<T>
{
    if |s| == 0 then
        multiset{}
    else
        multiset{s[0]} + multiset(s[1..])
}
// </vc-helpers>

// <vc-spec>
method uniqueSorted(s: seq<int>) returns (result: seq<int>)
    // pre-conditions-start
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
    // pre-conditions-end
    // post-conditions-start
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    if |s| == 0 then
        return [];
    
    var result := [s[0]];
    var i := 1;
    while i < |s| 
        invariant 0 <= i <= |s|
        invariant forall j, k :: 0 <= j < k < |result| ==> result[j] < result[k]
        invariant forall x :: x in result ==> x in s
        invariant (forall x :: x in s[0..i] ==> x in result)
        // Dafny 4.3 verification requires `s[0..i]` to be non-empty for `x in s[0..i]`
        invariant i > 0 ==> s[0] == result[0] 
        // This invariant replaces the one below. The original one is too strong a condition for the loop.
        // invariant forall x :: x in s[0..i] ==> x in result
    {
        if s[i] != result[|result|-1] then
            result := result + [s[i]];
        i := i + 1;
    }
    return result;
}
// </vc-code>

method unique(s: seq<int>) returns (result: seq<int>)
    // post-conditions-start
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
    // post-conditions-end
{
  assume{:axiom} false;
}
method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
{
  assume{:axiom} false;
}