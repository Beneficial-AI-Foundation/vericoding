// Rearranges the elements in an array 'a' of natural numbers,
// so that all odd numbers appear before all even numbers.

predicate  odd(n: nat) { n % 2 == 1 }
predicate  even(n: nat) { n % 2 == 0 }

// <vc-helpers>
function countOdd(a: array<nat>, start: int, end: int): int
  requires 0 <= start <= end <= a.Length
  reads a
  decreases end - start
{
  if start == end then 0 else (if odd(a[start]) then 1 else 0) + countOdd(a, start + 1, end)
}

lemma multisetPreserved(a: array<nat>, i: int, j: int)
  requires 0 <= i < j < a.Length
  ensures multiset(a[..]) == multiset(a[0..i] + a[i+1..j] + a[j+1..a.Length]) + multiset([a[i], a[j]])
{
}

lemma multisetSwapPreserved(a: array<nat>, i: int, j: int, oldA: seq<nat>)
  requires 0 <= i < j < a.Length
  requires oldA == a[..]
  ensures multiset(a[0..i] + [a[j]] + a[i+1..j] + [a[i]] + a[j+1..a.Length]) == multiset(oldA)
{
  calc {
    multiset(a[0..i] + [a[j]] + a[i+1..j] + [a[i]] + a[j+1..a.Length]);
    == multiset(a[0..i] + a[i+1..j] + a[j+1..a.Length]) + multiset([a[j], a[i]]);
    == multiset(a[0..i] + a[i+1..j] + a[j+1..a.Length]) + multiset([a[i], a[j]]);
    == multiset(oldA);
  }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method partitionOddEven(a: array<nat>) 
  modifies a
  ensures multiset(a[..]) == multiset(old(a[..]))
  ensures ! exists i, j :: 0 <= i < j < a.Length && even(a[i]) && odd(a[j])
// </vc-spec>
// </vc-spec>

// <vc-code>
method PartitionOddEven(a: array<nat>) 
  modifies a
  ensures multiset(a[..]) == multiset(old(a[..]))
  ensures !exists i, j :: 0 <= i < j < a.Length && even(a[i]) && odd(a[j])
{
  if a.Length <= 1 { return; }
  
  var i := 0;
  var j := a.Length - 1;
  
  while i < j
    decreases j - i
    invariant 0 <= i <= j <= a.Length
    invariant multiset(a[..]) == multiset(old(a[..]))
    invariant forall k :: 0 <= k < i ==> odd(a[k])
    invariant forall k :: j < k < a.Length ==> even(a[k])
  {
    if odd(a[i]) {
      i := i + 1;
    } else if even(a[j]) {
      j := j - 1;
    } else {
      var oldA := a[..];
      a[i], a[j] := a[j], a[i];
      assert multiset(a[0..i] + [a[j]] + a[i+1..j] + [a[i]] + a[j+1..a.Length]) == multiset(oldA) by {
        multisetSwapPreserved(a, i, j, oldA);
      }
      assert multiset(a[..]) == multiset(oldA);
      i := i + 1;
      j := j - 1;
    }
  }
}
// </vc-code>
