// <vc-preamble>
// Ghost predicate to check if a sequence is sorted in non-decreasing order
ghost predicate IsSorted(s: seq<real>)
{
    forall i, j :: 0 <= i < j < |s| ==> s[i] <= s[j]
}

// Ghost predicate to check if two sequences are permutations of each other
ghost predicate IsPermutation(s1: seq<real>, s2: seq<real>)
{
    |s1| == |s2| &&
    forall x :: Count(s1, x) == Count(s2, x)
}

// Ghost function to count occurrences of an element in a sequence
ghost function Count(s: seq<real>, x: real): nat
{
    if |s| == 0 then 0
    else (if s[0] == x then 1 else 0) + Count(s[1..], x)
}

// Ghost function that returns a sorted version of the input sequence
ghost function SortedVersion(s: seq<real>): seq<real>

// Ghost predicate that ensures SortedVersion produces a valid sorted permutation
ghost predicate SortedVersionValid(s: seq<real>)
{
    var sorted := SortedVersion(s);
    IsSorted(sorted) && IsPermutation(s, sorted)
}

// Axiom that SortedVersion always produces a valid result
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
lemma {:axiom} SortedVersionIsValid(s: seq<real>)
    ensures SortedVersionValid(s)

/**
 * Partitions an array around the k-th element.
 * Returns a rearranged copy where the k-th element is in its correct sorted position,
 * with smaller elements before it and equal/greater elements after it.
 */
method Partition(arr: seq<real>, kth: int) returns (result: seq<real>)
    requires 0 <= kth < |arr|
    ensures |result| == |arr|
    // All elements before kth position are <= the kth element
    ensures forall i :: 0 <= i < kth ==> result[i] <= result[kth]
    // All elements after kth position are >= the kth element
    ensures forall i :: kth < i < |result| ==> result[i] >= result[kth]
    // The k-th element is in its correct sorted position
    ensures SortedVersionValid(arr) ==> result[kth] == SortedVersion(arr)[kth]
    // The result is a permutation of the original array
    ensures IsPermutation(arr, result)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
