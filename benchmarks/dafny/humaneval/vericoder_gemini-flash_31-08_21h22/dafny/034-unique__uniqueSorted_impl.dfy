

// <vc-helpers>
function distinct(s: seq<int>): bool {
  forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

predicate contains(s: seq<int>, x: int) {
  exists i :: 0 <= i < |s| && s[i] == x
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
    var result_seq: seq<int> := [];
    if |s| == 0 {
        return [];
    }

    result_seq := [s[0]];
    var i := 1;
    while i < |s|
        invariant 1 <= i <= |s|
        invariant forall k, l :: 0 <= k < l < |result_seq| ==> result_seq[k] < result_seq[l]
        invariant forall x :: x in result_seq ==> x in s[..i]
        invariant forall k :: 0 <= k < i ==> (s[k] in result_seq) || (k > 0 && s[k] == s[k-1])
        invariant |result_seq| > 0 ==> result_seq[|result_seq|-1] == s[i-1]
        invariant forall x :: x in s[..i] ==> x in result_seq
    {
        if s[i] != s[i-1] {
            result_seq := result_seq + [s[i]];
        }
        i := i + 1;
    }
    return result_seq;
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