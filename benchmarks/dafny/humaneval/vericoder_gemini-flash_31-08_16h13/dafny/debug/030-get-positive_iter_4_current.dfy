

// <vc-helpers>
/**
 * `seq_contains` checks if a sequence `s` contains an element `e`.
 */
function seq_contains<T>(s: seq<T>, e: T): bool
{
  exists i :: 0 <= i < |s| && s[i] == e
}

/**
 * `seq_distinct` checks if all elements in a sequence `s` are distinct.
 */
function seq_distinct<T>(s: seq<T>): bool
{
  forall i, j :: 0 <= i < j < |s| ==> s[i] != s[j]
}

/**
 * `seq_subsequence` checks if `sub` is a subsequence of `main`.
 * That is, all elements of `sub` appear in `main` in the same order,
 * but not necessarily contiguously.
 */
function seq_subsequence<T>(main: seq<T>, sub: seq<T>): bool
  decreases sub
{
  if |sub| == 0 then
    true
  else if |main| == 0 then
    false
  else
    (main[0] == sub[0] && seq_subsequence(main[1..], sub[1..])) || seq_subsequence(main[1..], sub)
}

/**
 * `seq_permutation` checks if `s1` is a permutation of `s2`.
 * This means they have the same elements with the same frequencies.
 */
function seq_permutation<T>(s1: seq<T>, s2: seq<T>): bool
  requires T : !new
{
  |s1| == |s2| &&
  (forall e :: (count(s1, e) == count(s2, e)))
}

/**
 * `count` returns the number of occurrences of `e` in `s`.
 */
function count<T>(s: seq<T>, e: T): nat
{
  if |s| == 0 then
    0
  else if s[0] == e then
    1 + count(s[1..], e)
  else
    count(s[1..], e)
}

/**
 * `seq_of_set` checks if all elements of sequence `s` are present in set `m`.
 */
function seq_of_set<T>(s: seq<T>, m: set<T>): bool
{
  forall i :: 0 <= i < |s| ==> s[i] in m
}
// </vc-helpers>

// <vc-spec>
method get_positive(l : seq<int>) returns (result : seq<int>)
    // post-conditions-start
    ensures forall i : int :: i >= 0 && i < |result| ==> result[i] > 0
    ensures |result| <= |l|
    ensures forall i1 :: i1 >= 0 && i1 < |l| ==> (l[i1] > 0 ==> exists i2 :: i2 >= 0 && i2 < |result| && result[i2] == l[i1])
    ensures |result| == 0 || (forall i1 : int :: i1 >= 0 && i1 < |result| ==> (exists i2 :: i2 >= 0 && i2 < |l| && l[i2] == result[i1]))
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
    var result_seq: seq<int> := [];
    var i := 0;
    while i < |l|
      invariant 0 <= i <= |l|
      invariant forall k :: 0 <= k < |result_seq| ==> result_seq[k] > 0
      invariant forall k :: 0 <= k < |result_seq| ==> (exists j :: 0 <= j < i && l[j] == result_seq[k])
      invariant forall k :: 0 <= k < i ==> (l[k] > 0 ==> exists j :: 0 <= j < |result_seq| && result_seq[j] == l[k])
      invariant |result_seq| <= i // This implies |result_seq| <= |l|
    {
        if l[i] > 0 {
            result_seq := result_seq + [l[i]];
        }
        i := i + 1;
    }
    return result_seq;
}
// </vc-code>

