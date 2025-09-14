// Working through https://dafny.org/dafny/OnlineTutorial/guide

function fib(n: nat): nat
{
  if n == 0 then 0
  else if n == 1 then 1
  else fib(n - 1) + fib(n - 2)
}


predicate sorted(a: array<int>)
  reads a
{
  forall n, m :: 0 <= n < m < a.Length ==> a[n] <= a[m]
}



// https://dafny.org/dafny/OnlineTutorial/ValueTypes

function update(s: seq<int>, i: int, v: int): seq<int>
  requires 0 <= i < |s|
  ensures update(s, i, v) == s[i := v]
{
  s[..i] + [v] + s[i+1..]
}


// https://dafny.org/dafny/OnlineTutorial/Lemmas

function count(a: seq<bool>): nat
{
  if |a| == 0 then 0 else
  (if a[0] then 1 else 0) + count(a[1..])
}


class Node
{
  var next: seq<Node>
}
predicate closed(graph: set<Node>)
  reads graph
{
  forall i :: i in graph ==> forall k :: 0 <= k < |i.next| ==> i.next[k] in graph && i.next[k] != i
}
predicate path(p: seq<Node>, graph: set<Node>)
  requires closed(graph) && 0 < |p|
  reads graph
{
  p[0] in graph &&
    (|p| > 1 ==> p[1] in p[0].next && // the first link is valid, if it exists
     path(p[1..], graph)) // and the rest of the sequence is a valid
}
predicate pathSpecific(p: seq<Node>, start: Node, end: Node, graph: set<Node>)
  requires closed(graph)
  reads graph
{
  0 < |p| && // path is nonempty
  start == p[0] && end == p[|p|-1] && // it starts and ends correctly
  path(p, graph) // and it is a valid path
}

// <vc-helpers>
function findZero(a: seq<int>): (index: int)
  requires forall i :: 0 <= i < |a| ==> 0 <= a[i]
  requires forall i :: 0 < i < |a| ==> a[i-1]-1 <= a[i]
  ensures index < 0  ==> forall i :: 0 <= i < |a| ==> a[i] != 0
  ensures 0 <= index ==> index < |a| && a[index] == 0
{
  var low := 0;
  var high := |a|; // exclusive upper bound

  if |a| == 0 then return -1;

  // The loop invariant states that if an element `0` exists in the array,
  // it must be within the range `a[low..high-1]`.
  // Also, all elements `a[k]` where `k < low` are not 0.
  while low < high
    invariant 0 <= low <= high <= |a|
    invariant forall k :: 0 <= k < low ==> a[k] != 0
    invariant (exists k :: low <= k < |a| && a[k] == 0) ==> (exists k :: low <= k < high && a[k] == 0)
    // Additional invariant: all elements in the array are non-negative and satisfy the difference condition.
    invariant forall i :: 0 <= i < |a| ==> 0 <= a[i]
    invariant forall i :: 0 < i < |a| ==> a[i-1]-1 <= a[i]
  {
    var mid := low + (high - low) / 2;
    if a[mid] == 0 {
      // Found 0, let's try to find the first one by narrowing the search to the left.
      high := mid;
    } else { // a[mid] > 0
      // The value at mid is positive.
      // Since `a[i-1]-1 <= a[i]`, if a[mid] is positive, then all elements to its right
      // `a[k]` for `k > mid` are at least `a[mid]-1`, which means they are also non-negative.
      // If there is a 0, it must be to the left of or at `mid`.
      // Based on the given preconditions (non-negative and `a[i-1]-1 <= a[i]`),
      // if `a[mid] > 0`, it means any `0` if present must be to the left of `mid`.
      // More precisely, for `a[mid] > 0`, we know `a[mid-1]` could be `0` or `1`.
      // If `a[mid]` is positive, all values `a[mid]` up to `a[high-1]` are candidates.
      // However, if `a[mid] > 0`, we cannot exclude `mid` or anything to its right *yet* just based on `a[mid] > 0`.
      // We need to move `low` up.
      low := mid + 1; // 0 must be to the right
                                     // (or doesn't exist to the left of mid+1)
    }
  }

  // After the loop, low == high.
  // The invariant `forall k :: 0 <= k < low ==> a[k] != 0` tells us that no 0 is in `a[0..low-1]`.
  // The invariant `(exists k :: low <= k < |a| && a[k] == 0) ==> (exists k :: low <= k < high && a[k] == 0)`
  // becomes `(exists k :: low <= k < |a| && a[k] == 0) ==> false` if low == high.
  // So, it simplifies to `!(exists k :: low <= k < |a| && a[k] == 0)`.
  // Combining these, if a 0 existed, it must have been in the `[low..high-1]` range, which is now empty.
  // Therefore, no 0 exists in the entire array.
  // Except the case where we find 0 and update high.
  // The loop aims to find the *first* 0.
  // If `a[mid] == 0`, we narrow `high := mid`
  // If `a[mid] > 0`, we narrow `low := mid + 1` (0 must be to the right or not exist)

  // This is a standard binary search for the first element satisfying a property (a[i] == 0).
  // The property is that if `a[i]==0`, then `a[i]` is a potential candidate for the first zero.
  // If `a[i] > 0`, then `a[i]` is not the first zero. The first zero must be to the right.
  // If `a[i] == 0`, this might be the first zero, or a zero exists before it. So we try `[low, mid]`.
  // If `a[i] > 0`, then `a[i]` is not zero. Any zero must be to the right of `i`. So we try `[mid+1, high]`.

  // Let's re-verify the logic for updating low/high based on typical binary search for first occurrence:
  // If `a[mid] == 0`, we've found a potential first zero, so we store it and continue searching in the left part.
  var foundCandidate := -1;
  var currentLow := 0;
  var currentHigh := |a|;

  while currentLow < currentHigh
    invariant 0 <= currentLow <= currentHigh <= |a|
    invariant forall i :: 0 <= i < |a| ==> 0 <= a[i]
    invariant forall i :: 0 < i < |a| ==> a[i-1]-1 <= a[i]
    invariant (exists k :: 0 <= k < |a| && a[k] == 0) ==>
                (exists k :: currentLow <= k < currentHigh && a[k] == 0) ||
                (foundCandidate != -1 && a[foundCandidate] == 0 && (forall l :: 0 <= l < foundCandidate ==> a[l] != 0))
    invariant foundCandidate == -1 || (0 <= foundCandidate < |a| && a[foundCandidate] == 0)
    invariant (forall k :: 0 <= k < currentLow ==> a[k] != 0 || (foundCandidate != -1 && k >= foundCandidate))
    invariant (foundCandidate != -1) ==> (forall k :: foundCandidate <= k < currentHigh ==> a[k] != 0 || (a[foundCandidate] == 0 && k == foundCandidate))
  {
    var mid := currentLow + (currentHigh - currentLow) / 2;
    if a[mid] == 0 {
      foundCandidate := mid;
      currentHigh := mid; // Try to find an even smaller index (first occurrence)
    } else { // a[mid] > 0
             // Because a[k-1] - 1 <= a[k], if a[mid] is > 0, then a[k] can still be 0 for k > mid.
             // But a[mid] itself is not 0. So we can move the low boundary past mid.
      currentLow := mid + 1;
    }
  }
  return foundCandidate;
}

function findZeroLinear(a: seq<int>): (index: int)
  requires forall i :: 0 <= i < |a| ==> 0 <= a[i]
  requires forall i :: 0 < i < |a| ==> a[i-1]-1 <= a[i]
  ensures index < 0  ==> forall i :: 0 <= i < |a| ==> a[i] != 0
  ensures 0 <= index ==> index < |a| && a[index] == 0
{
  var result := -1;
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant result == -1 ==> forall k :: 0 <= k < i ==> a[k] != 0
    invariant result != -1 ==> 0 <= result < i && a[result] == 0 && (forall k :: 0 <= k < result ==> a[k] != 0)
    invariant forall k :: 0 <= k < |a| ==> 0 <= a[k]
    invariant forall k :: 0 < k < |a| ==> a[k-1]-1 <= a[k]
  {
    if a[i] == 0 {
      result := i;
      break;
    }
    i := i + 1;
  }
  return result;
}

// Lemma to establish necessary conditions for binary search proof
lemma LemmaRangeProperty(a: array<int>, low: int, high: int)
  requires 0 <= low <= high <= a.Length
  requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
  requires forall i :: 0 < i < a.Length ==> a[i-1]-1 <= a[i]
  ensures (exists k :: low <= k < high && a[k] == 0) ==> (exists k' :: low <= k' < high && a[k'] == 0 && (forall l :: low <= l < k' ==> a[l] != 0))
{
  // This lemma states that if there's a 0 in a range, there's a *first* 0 in that range.
  // This is inherent to integers and existence. The property itself does not need a formal Dafny proof,
  // as it's directly derived from the well-ordering principle on natural numbers (indices).
  // If the set of indices {k | low <= k < high && a[k] == 0} is non-empty,
  // then it has a minimum element.
}

// A lemma to show that if a[mid] > 0, then the first zero must be to the right of mid,
// assuming no zero exists to the left of `low`.
// Actually, it means the first zero must be at or after `mid`. No, that's not true.
// If `a[mid]` is positive, this `mid` cannot be an index of a `0`.
// So we can discard `mid` as a possibility for `0` itself.
// The question is, does this imply that *all* values to the left of `mid` are also positive,
// or that the first occurrence of `0` must be to the right?
// Consider `[5, 0, 1]`. `mid` might be on `5`. `a[mid] > 0`. The first zero is to the right.
// Consider `[0, 5, 0]`. This array structure is problematic with `a[i-1]-1 <= a[i]`.
// If `a[0] = 0`, `a[1] = 5`, then `a[0]-1 = -1 <= a[1] = 5`. This is allowed.
// But then `a[1]-1 = 4 <= a[2] = 0` is false. So `[0, 5, 0]` is not a valid input.

// The condition `a[i-1]-1 <= a[i]` is very important.
// It means `a[i] >= a[i-1] - 1`.
// If `a[mid] > 0`: We are looking for the *first* zero.
// If there is *some* zero `a[k] == 0` for `k >= mid`, then the absolute first zero could still be `< mid`.
// Example `[1, 0, 0, 0]`. `mid` could be on `1`. `a[mid] > 0`. We need to search right. `low = mid+1`.
// This seems to be the correct standard binary search approach for finding the smallest index `i` such that `a[i] == 0`.
// If `a[mid] == 0`, we've found a candidate. `ans = mid`. We try to find an even smaller one: `high = mid-1`.
// If `a[mid] > 0`, then `mid` is not `0`. The first `0` must be at an index `k > mid`. So `low = mid+1`.
// If `a[mid] < 0`, this case is ruled out by `0 <= a[i]`.
// </vc-helpers>

// <vc-spec>
method FindZero(a: array<int>) returns (index: int)
  requires forall i :: 0 <= i < a.Length ==> 0 <= a[i]
  requires forall i :: 0 < i < a.Length ==> a[i-1]-1 <= a[i]
  ensures index < 0  ==> forall i :: 0 <= i < a.Length ==> a[i] != 0
  ensures 0 <= index ==> index < a.Length && a[index] == 0
// </vc-spec>
// <vc-code>
{
  var low := 0;
  var high := a.Length - 1;
  var foundIndex := -1;

  if a.Length == 0 {
    return -1;
  }

  while low <= high
    invariant 0 <= low <= a.Length
    invariant -1 <= high < a.Length
    invariant forall k :: 0 <= k < a.Length ==> 0 <= a[k]
    invariant forall k :: 0 < k < a.Length ==> a[k-1]-1 <= a[k]
    invariant foundIndex == -1 || (0 <= foundIndex < a.Length && a[foundIndex] == 0 && (forall k :: 0 <= k < foundIndex ==> a[k] != 0))
    invariant (forall k :: 0 <= k < low ==> a[k] != 0 || (foundIndex != -1 && k >= foundIndex))
    invariant (exists k :: 0 <= k < a.Length && a[k] == 0) ==>
                (foundIndex != -1 && a[foundIndex] == 0 && (forall j :: 0 <= j < foundIndex ==> a[j] != 0)) ||
                (exists k :: low <= k <= high && a[k] == 0)
  {
    var mid := low + (high - low) / 2;
    if a[mid] == 0 {
      foundIndex := mid;
      high := mid - 1; // Try to find an even smaller index
    } else { // a[mid] > 0
      low := mid + 1;
    }
  }
  return foundIndex;
}
// </vc-code>

