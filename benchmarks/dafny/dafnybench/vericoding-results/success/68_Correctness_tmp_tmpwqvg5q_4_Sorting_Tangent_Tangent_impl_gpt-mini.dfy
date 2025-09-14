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
// (No helper code needed)
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
  var fi := -1;
  var fj := -1;
  var i := 0;
  while i < r.Length && !found
    invariant 0 <= i <= r.Length
    invariant (found ==> 0 <= fi < r.Length && 0 <= fj < x.Length && r[fi] == x[fj])
    invariant (!found) ==> (forall i0 :: 0 <= i0 < i ==> forall j0 :: 0 <= j0 < x.Length ==> r[i0] != x[j0])
    decreases r.Length - i
  {
    var j := 0;
    while j < x.Length && !found
      invariant 0 <= j <= x.Length
      invariant (found ==> 0 <= fi < r.Length && 0 <= fj < x.Length && r[fi] == x[fj])
      invariant (!found) ==> (forall j0 :: 0 <= j0 < j ==> r[i] != x[j0])
      decreases x.Length - j, if !found then 1 else 0
    {
      if r[i] == x[j] {
        found := true;
        fi := i;
        fj := j;
      } else {
        j := j + 1;
      }
    }
    i := i + 1;
  }
}
// </vc-code>

