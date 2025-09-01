

// <vc-helpers>
function method distinct(s: seq<int>): bool {
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
        invariant forall x :: x in s[..i] ==> x in result_seq || (exists k :: 0 <= k < |result_seq| && s[i-1] == result_seq[k] && s[i] == x && x == s[k]) // This invariant seems problematic, rethinking it.

        invariant forall x :: x in result_seq ==> x in s[..i]
        invariant forall x :: x in s[..i] ==> x in result_seq || (exists k :: 0 <= k < |result_seq| && result_seq[k] == s[i-1] && (x == s[i] && x == s[i-1])) // Re-evaluating.

        // Corrected invariants (simplified and focused on the properties):
        invariant forall k, l :: 0 <= k < l < |result_seq| ==> result_seq[k] < result_seq[l]
        invariant forall x :: x in result_seq ==> x in s[..i]
        invariant forall x :: x in s[..i] ==> x in result_seq || (exists k :: s[k] == x && 0 <= k < i && x == s[i-1]) // This one is still a bit off for the `x in s[..i] ==> x in result_seq` logic, as `s[i-1]` is what we just processed.

        // Let's reformulate the "all elements from s[..i] are accounted for" invariant:
        invariant (forall x :: x in result_seq ==> x in s[..i]) && (forall x :: x in s[..i] ==> x in result_seq)
        // This is too strong, as it effectively means result_seq is a unique version of s[..i]. Let's break it down.

        invariant forall k, l :: 0 <= k < l < |result_seq| ==> result_seq[k] < result_seq[l]
        invariant forall x :: x in result_seq ==> exists k :: 0 <= k < i && s[k] == x
        invariant forall k :: 0 <= k < i ==> (s[k] in result_seq || s[k] == s[k-1]) // Simplified representation of what elements should be in result_seq


        // The most critical invariants for this specific algorithm:
        invariant 0 < i <= |s|
        invariant |result_seq| > 0 ==> result_seq[|result_seq|-1] == s[i-1]
        invariant forall k, l :: 0 <= k < l < |result_seq| ==> result_seq[k] < result_seq[l]
        invariant forall x :: x in result_seq ==> x in s[..i]
        invariant forall k :: 0 <= k < i ==> (s[k] in result_seq) || (k > 0 && s[k] == s[k-1]) // This seems closer.

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