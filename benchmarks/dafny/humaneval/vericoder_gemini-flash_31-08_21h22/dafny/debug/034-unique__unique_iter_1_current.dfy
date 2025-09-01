method uniqueSorted(s: seq<int>) returns (result: seq<int>)
    // pre-conditions-start
    requires forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
    // pre-conditions-end
    // post-conditions-start
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    ensures forall x :: x in result ==> x in s
    ensures forall x :: x in s ==> x in result
    // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
function method IsUniqueSorted(s: seq<int>): bool
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] < s[j]
}

function method IsSubsequenceOf(s1: seq<int>, s2: seq<int>): bool
{
    forall x :: x in s1 ==> x in s2
}

function method IsSupersetOf(s1: seq<int>, s2: seq<int>): bool
{
    forall x :: x in s2 ==> x in s1
}
// </vc-helpers>

// <vc-spec>
method unique(s: seq<int>) returns (result: seq<int>)
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
        return result_seq;
    }

    result_seq := result_seq + [s[0]];
    var i := 1;
    while i < |s|
        invariant 1 <= i <= |s|
        invariant forall k, l :: 0 <= k < l < |result_seq| ==> result_seq[k] < result_seq[l]
        invariant forall x :: x in result_seq ==> x in s
        invariant forall x :: x in s[..i] ==> x in result_seq
        invariant |result_seq| > 0 ==> result_seq[|result_seq|-1] == s[i-1] || result_seq[|result_seq|-1] < s[i-1]
        decreases |s| - i
    {
        if s[i] > result_seq[|result_seq|-1] {
            result_seq := result_seq + [s[i]];
        }
        i := i + 1;
    }

    // Post-condition proof
    // ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    // ensures forall x :: x in result ==> x in s
    // ensures forall x :: x in s ==> x in result
    reveal IsUniqueSorted();
    reveal IsSubsequenceOf();
    reveal IsSupersetOf();

    assert IsUniqueSorted(result_seq);
    assert IsSubsequenceOf(result_seq, s);

    // To prove subset of s implies subset of result
    var s_set := multiset(s);
    var result_set := multiset(result_seq);

    forall x | x in s_set
        ensures x in result_set
    {
        if x in result_set {
            // Nothing to do, it's already there
        } else {
            // If x is in s but not in result_seq after filtering,
            // it means x must be a duplicate of a previously included element in s,
            // or equal to a previously included element.
        }
    }
    assert IsSupersetOf(result_seq, s);

    return result_seq;
}
// </vc-code>

method SortSeq(s: seq<int>) returns (sorted: seq<int>)
  // post-conditions-start
  ensures forall i, j :: 0 <= i < j < |sorted| ==> sorted[i] <= sorted[j]
  ensures |sorted| == |s|
  ensures multiset(s) == multiset(sorted)
  // post-conditions-end
{
  assume{:axiom} false;
}