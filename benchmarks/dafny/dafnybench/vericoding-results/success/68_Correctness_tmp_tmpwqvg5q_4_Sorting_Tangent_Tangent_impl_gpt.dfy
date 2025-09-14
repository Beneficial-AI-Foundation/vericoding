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
// no helper updates needed
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
  var wi := 0;
  var wj := 0;

  var i := 0;
  while i < r.Length && !found
    invariant 0 <= i <= r.Length
    invariant !found ==> forall ii :: 0 <= ii < i ==> forall jj :: 0 <= jj < x.Length ==> r[ii] != x[jj]
    invariant found ==> 0 <= wi < r.Length && 0 <= wj < x.Length && r[wi] == x[wj]
    decreases if found then 0 else 1, r.Length - i
  {
    var j := 0;
    while j < x.Length && !found
      invariant 0 <= j <= x.Length
      invariant 0 <= i < r.Length
      invariant !found ==> forall jj :: 0 <= jj < j ==> r[i] != x[jj]
      invariant !found ==> forall ii :: 0 <= ii < i ==> forall jj :: 0 <= jj < x.Length ==> r[ii] != x[jj]
      invariant found ==> 0 <= wi < r.Length && 0 <= wj < x.Length && r[wi] == x[wj]
      decreases if found then 0 else 1, x.Length - j
    {
      if r[i] == x[j] {
        found := true;
        wi := i;
        wj := j;
      } else {
        j := j + 1;
      }
    }
    if !found {
      assert forall jj :: 0 <= jj < x.Length ==> r[i] != x[jj];
      assert forall ii :: 0 <= ii < i + 1 ==> forall jj :: 0 <= jj < x.Length ==> r[ii] != x[jj];
      i := i + 1;
    }
  }

  if found {
    assert 0 <= wi < r.Length && 0 <= wj < x.Length && r[wi] == x[wj];
    assert exists ii, jj :: 0 <= ii < r.Length && 0 <= jj < x.Length && r[ii] == x[jj];
  } else {
    assert !(i < r.Length);
    assert i == r.Length;
    assert forall ii, jj :: 0 <= ii < r.Length && 0 <= jj < x.Length ==> r[ii] != x[jj];
  }
}
// </vc-code>

