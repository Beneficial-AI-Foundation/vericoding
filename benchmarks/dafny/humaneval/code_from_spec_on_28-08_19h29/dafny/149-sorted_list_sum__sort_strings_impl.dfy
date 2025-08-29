function comparison(a : string, b : string, i : int): bool
    requires 0 <= i <= |a| && 0 <= i <= |b|
    decreases |a| - i
    decreases |b| - i
    ensures (a == b) ==> comparison(a, b, i)
{
    if (i < |a| && i < |b|) then
        if a[i] < b[i] then
            true
        else if a[i] > b[i] then
            false
        else
            comparison(a, b, i + 1)
    else
        if |a| <= |b| then
            true
        else
            false
}

// <vc-helpers>
// Helper lemma to prove properties about sorted sequences
lemma SortedPermutation(list: seq<string>, sorted: seq<string>)
  requires multiset(sorted) == multiset(list)
  requires forall x, y : int :: 0 <= x < y < |sorted| ==> comparison(sorted[x], sorted[y], 0)
  ensures forall x, y : int :: 0 <= x < y < |sorted| ==> comparison(sorted[x], sorted[y], 0)
{
}

// Lemma to establish comparison transitivity
lemma ComparisonTransitivity(a: string, b: string, c: string)
  requires comparison(a, b, 0)
  requires comparison(b, c, 0)
  ensures comparison(a, c, 0)
{
  var i := 0;
  while i < |a| && i < |b| && i < |c|
    invariant 0 <= i <= |a| && 0 <= i <= |b| && 0 <= i <= |c|
    invariant forall k :: 0 <= k < i ==> a[k] == b[k] && b[k] == c[k]
    decreases |a| - i, |b| - i, |c| - i
  {
    if a[i] < b[i] || b[i] < c[i] {
      break;
    }
    i := i + 1;
  }
}

// Helper lemma to prove comparison holds after swaps
lemma ComparisonHoldsAfterSwap(result: seq<string>, i: int, minIndex: int)
  requires 0 <= i < |result|
  requires 0 <= minIndex < |result|
  requires forall x, y : int :: 0 <= x < y < i ==> comparison(result[x], result[y], 0)
  requires forall k : int :: i <= k < |result| ==> comparison(result[minIndex], result[k], 0) || result[minIndex] == result[k]
  ensures forall x, y : int :: 0 <= x < y < i + 1 ==> comparison(result[i := result[minIndex]][minIndex := result[i]][x], result[i := result[minIndex]][minIndex := result[i]][y], 0)
{
  var swapped := result[i := result[minIndex]][minIndex := result[i]];
  forall x, y | 0 <= x < y < i + 1
    ensures comparison(swapped[x], swapped[y], 0)
  {
    if y == i {
      assert comparison(swapped[x], swapped[i], 0) by {
        if x < i {
          assert comparison(result[x], result[minIndex], 0) || result[x] == result[minIndex];
          if result[x] == result[minIndex] {
            assert swapped[x] == swapped[i];
          } else {
            assert comparison(result[x], result[minIndex], 0);
            assert swapped[i] == result[minIndex];
            assert comparison(swapped[x], swapped[i], 0);
          }
        }
      }
    } else {
      assert comparison(swapped[x], swapped[y], 0);
    }
  }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method sort_strings(list: seq<string>) returns (sorted: seq<string>)
Sort elements. Ensures: returns the correct size/count; returns a sorted permutation of the input.
*/
// </vc-description>

// <vc-spec>
method sort_strings(list: seq<string>) returns (sorted: seq<string>)
  requires true
  ensures |sorted| == |list|
  ensures multiset(sorted) == multiset(list)
  ensures forall x, y : int :: 0 <= x < y < |sorted| ==> comparison(sorted[x], sorted[y], 0)
// </vc-spec>
// <vc-code>
{
  var n := |list|;
  if n == 0 {
    return [];
  }
  
  var result := list;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |result| == n
    invariant multiset(result) == multiset(list)
    invariant forall x, y : int :: 0 <= x < y < i ==> comparison(result[x], result[y], 0)
  {
    var minIndex := i;
    var j := i + 1;
    while j < n
      invariant i <= j <= n
      invariant i <= minIndex < n
      invariant forall k : int :: i <= k < j ==> comparison(result[minIndex], result[k], 0) || result[minIndex] == result[k]
    {
      if !comparison(result[minIndex], result[j], 0) && result[minIndex] != result[j] {
        minIndex := j;
      }
      j := j + 1;
    }
    if minIndex != i {
      var temp := result[i];
      result := result[i := result[minIndex]][minIndex := temp];
      ComparisonHoldsAfterSwap(result, i, minIndex);
    }
    i := i + 1;
  }
  return result;
}
// </vc-code>

method sort_lengths(list: seq<string>) returns (sorted: seq<string>)
    requires forall i : int :: 0 <= i < |list| ==> |list[i]| % 2 == 0
    ensures forall i : int :: 0 <= i < |sorted| ==> |sorted[i]| % 2 == 0
    ensures |sorted| == |list|
    ensures multiset(sorted) == multiset(list)
    ensures forall x : int, y : int :: 0 <= x < y < |sorted| ==> |sorted[x]| <= |sorted[y]|
{
  assume{:axiom} false;
}
method sorted_list_sum(list: seq<string>) returns (sorted: seq<string>)
    requires |list| > 0
    ensures |sorted| <= |list|
    ensures forall i : int :: 0 <= i < |sorted| ==> |sorted[i]| % 2 == 0
    ensures forall x : int, y : int :: 0 <= x < y < |sorted| ==> |sorted[x]| <= |sorted[y]|
    ensures multiset(sorted) <= multiset(list)
{
  assume{:axiom} false;
}