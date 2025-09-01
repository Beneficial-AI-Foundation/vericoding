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
function IsUniqueSorted(s: seq<int>): bool
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] < s[j]
}

function IsSubsequenceOf(s1: seq<int>, s2: seq<int>): bool
{
    forall x :: x in s1 ==> x in s2
}

function IsSupersetOf(s1: seq<int>, s2: seq<int>): bool
{
    forall x :: x in s2 ==> x in s1
}

ghost predicate UniqueElementsInPrefixReflected(s: seq<int>, result_seq: seq<int>, i: int)
  requires 0 <= i <= |s|
  requires forall k, l :: 0 <= k < l < |result_seq| ==> result_seq[k] < result_seq[l]
{
  forall x :: x in s[..i] && (forall k :: 0 <= k < i && k < |s| && s[k] != x ==> true) ==> x in result_seq
}

ghost predicate UniqueCheck(s: seq<int>, result_seq: seq<int>, i: int)
  requires 0 <= i <= |s|
  requires forall k, l :: 0 <= k < l < |result_seq| ==> result_seq[k] < result_seq[l]
{
  forall x :: (exists k :: 0 <= k < i && s[k] == x) &&
              (forall k' :: 0 <= k' < i && s[k'] == x ==> k' == (var idx := k; forall k_prev :: 0 <= k_prev < k && s[k_prev] == x ==> idx := k_prev; idx)) ==> x in result_seq
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
        invariant forall x :: x in result_seq ==> x in s[..i] // Elements in result_seq are from s up to index i-1.
        invariant forall x :: (exists j :: 0 <= j < i && s[j] == x && (forall k :: 0 <= k < j && s[k] != x)) ==> x in result_seq
        invariant |result_seq| > 0 ==> result_seq[|result_seq|-1] <= s[i-1] // Last element of result_seq is less than or equal to s[i-1]
        invariant |result_seq| > 0 ==> (i < |s| ==> result_seq[|result_seq|-1] < s[i])
        decreases |s| - i
    {
        if s[i] > result_seq[|result_seq|-1] {
            result_seq := result_seq + [s[i]];
        } else {
            // Since s is sorted, if s[i] is not greater than result_seq[|result_seq|-1],
            // then s[i] must be equal to result_seq[|result_seq|-1].
            // If it were lesser, it would violate s being sorted.
            // So, s[i] is a duplicate and is skipped.
            assert s[i] == result_seq[|result_seq|-1]; // This is implied by the sorted property of s and a previous invariant.
        }
        i := i + 1;
    }

    // Post-condition proof
    // ensures forall i, j :: 0 <= i < j < |result| ==> result[i] < result[j]
    assert IsUniqueSorted(result_seq); // Follows from the loop invariant

    // ensures forall x :: x in result ==> x in s
    assert forall x :: x in result_seq ==> x in s[..|s|];
    assert IsSubsequenceOf(result_seq, s); // Follows from loop invariant

    // ensures forall x :: x in s ==> x in result
    // This is the tricky part. We need to show that every element in s is either in result_seq,
    // or it's a duplicate of an element that is in result_seq.
    // Since result_seq contains only unique elements, and s is sorted (allowing duplicates),
    // we need to show that `multiset(s)` restricted to unique values equals `multiset(result_seq)`.
    // Or equivalently, for any x in s, x must exist in result_seq.
    forall x | x in s
        ensures x in result_seq
    {
        var k: int := 0;
        while k < |s|
            invariant 0 <= k <= |s|
            invariant forall y :: (exists j :: 0 <= j < k && s[j] == y) && (forall j_prev :: 0 <= j_prev < j && s[j_prev] == y ==> j_prev == j) ==> y in result_seq
        {
          if (exists j :: 0 <= j < k && s[j] == s[k] == x) { // x is a duplicate found earlier in s
          } else { // x is the first occurrence of this value
            assert (exists j :: 0 <= j < |s| && s[j] == x && (forall k_prime :: 0 <= k_prime < j && s[k_prime] != x));
            assert x in result_seq; // From the loop invariant of the unique method
          }
          k := k + 1;
        }
    }
    assert IsSupersetOf(result_seq, s); // This is effectively proven by the loop invariants and the structure of the algorithm.

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