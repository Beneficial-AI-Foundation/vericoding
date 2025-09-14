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
lemma BinarySearchCorrectness(a: array<int>, target: int, result: int)
  requires forall i :: 1 <= i < a.Length ==> a[i-1] < a[i]
  requires forall i, j :: 0 <= i < j < a.Length ==> a[i] < a[j]
  requires 0 <= result <= a.Length
  requires forall i :: 0 <= i < result ==> a[i] < target
  requires forall i :: result <= i < a.Length ==> target <= a[i]
  ensures result == a.Length || a[result] >= target
  ensures result == 0 || a[result-1] < target
{
}

lemma ArraySearchProperty(r: array<int>, x: array<int>, found: bool, witness_i: int, witness_j: int)
  requires found ==> (0 <= witness_i < r.Length && 0 <= witness_j < x.Length && r[witness_i] == x[witness_j])
  requires !found ==> forall i,j :: 0 <= i < r.Length && 0 <= j < x.Length ==> r[i] != x[j]
  ensures found <==> exists i,j :: 0 <= i < r.Length && 0 <= j < x.Length && r[i] == x[j]
{
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
    invariant !found ==> forall k,j :: 0 <= k < i && 0 <= j < x.Length ==> r[k] != x[j]
    invariant found ==> exists k,j :: 0 <= k < r.Length && 0 <= j < x.Length && r[k] == x[j]
  {
    var result := BinarySearch(x, r[i]);
    
    if result < x.Length && x[result] == r[i] {
      found := true;
    }
    
    i := i + 1;
  }
}
// </vc-code>

