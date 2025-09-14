/**
  Ather, Mohammad Faiz (s4648481/3)
  CSSE3100
  Assignemnt 3
  The University of Queensland
 */

// Question 1

// Author: Leino, Title: Program Proofs
method BinarySearch(a: array<int>, circle: int)
  returns (n: int)
  requires forall i ::
           1 <= i < a.Length
           ==> a[i-1] < a[i]
  requires forall i, j ::
           0 <= i < j < a.Length ==>
           a[i] < a[j]
  ensures 0 <= n <= a.Length
  ensures forall i ::
          0 <= i < n ==>
          a[i] < circle
  ensures forall i ::
          n <= i < a.Length ==>
          circle <= a[i]
{
  assume{:axiom} false;
}

// <vc-helpers>
predicate IsSorted(a: array<int>)
  reads a
{
  forall i :: 1 <= i < a.Length ==> a[i-1] < a[i]
}
// </vc-helpers>

// <vc-spec>
method Tangent(r: array<int>, x: array<int>)
  returns (found: bool)
  requires forall i:: 1 <= i < x.Length ==> 
           x[i-1] < x[i]
  requires forall i, j ::
           0 <= i < j < x.Length ==>
           x[i] < x[j]
  ensures !found ==>
          forall i,j ::
          0 <= i < r.Length &&
          0 <= j < x.Length ==>
          r[i] != x[j]
  ensures found ==>
          exists i,j ::
          0 <= i < r.Length &&
          0 <= j < x.Length &&
          r[i] == x[j]
// </vc-spec>
// <vc-code>
{
  found := false;
  var i := 0;
  while i < r.Length && !found
    invariant 0 <= i <= r.Length
    invariant !found ==> forall idx, k :: 0 <= idx < i && 0 <= k < x.Length ==> r[idx] != x[k]
    invariant found ==> exists idx, k :: 0 <= idx < i && 0 <= k < x.Length && r[idx] == x[k]
  {
    var j := 0;
    while j < x.Length && !found && x[j] <= r[i]
      invariant 0 <= j <= x.Length
      invariant !found ==> forall k :: 0 <= k < j ==> x[k] != r[i]
      invariant found ==> exists k :: 0 <= k < j && x[k] == r[i]
    {
      if x[j] == r[i] {
        found := true;
      }
      j := j + 1;
    }
    i := i + 1;
  }
}
// </vc-code>

