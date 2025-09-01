

// <vc-helpers>
lemma UniqueSortedLemma(s: seq<int>)
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
    ensures forall x :: x in s ==> x in s
{
}

lemma RemoveDuplicatesLemma(s: seq<int>, i: int)
    requires 0 <= i < |s|
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
    ensures s[i] in s
{
}

lemma ResultOrderingLemma(result: seq<int>)
    requires forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
{
}

lemma MembershipLemma(s: seq<int>, result: seq<int>)
    requires forall x :: x in result ==> x in s
    requires forall x :: x in s ==> x in result
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
{
}

lemma StrictOrderingLemma(s: seq<int>)
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
    ensures forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
{
}

lemma MonotonicityLemma(s: seq<int>, i: int, j: int)
    requires 0 <= i <= j <= |s|
    requires forall k, l :: 0 <= k < l < |s| ==> s[k] <= s[l]
    ensures forall k, l :: 0 <= k < l < |s[i..j]| ==> s[i..j][k] <= s[i..j][l]
{
}

lemma LoopInvariantLemma(s: seq<int>, result: seq<int>, i: int)
    requires 0 <= i <= |s|
    requires forall k, l :: 0 <= k < l < |s| ==> s[k] <= s[l]
    requires forall k, l :: 0 <= k < l < |result| ==> result[k] < result[l]
    requires forall x :: x in result ==> x in s
    requires forall x :: x in s[0..i] ==> x in result
    ensures forall x :: x in s[0..i] ==> x in result
{
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
    if |s| == 0 {
        result := [];
    } else {
        var i := 1;
        result := [s[0]];
        while i < |s|
            invariant 0 <= i <= |s|
            invariant forall k, l :: 0 <= k < l < |result| ==> result[k] < result[l]
            invariant forall x :: x in result ==> x in s
            invariant forall x :: x in s[0..i] ==> x in result
            invariant |result| > 0 ==> result[|result|-1] == s[i-1]
        {
            if i < |s| {
                if s[i] > result[|result|-1] {
                    result := result + [s[i]];
                } else if s[i] == result[|result|-1] {
                    // Skip duplicate
                }
            }
            i := i + 1;
        }
    }
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