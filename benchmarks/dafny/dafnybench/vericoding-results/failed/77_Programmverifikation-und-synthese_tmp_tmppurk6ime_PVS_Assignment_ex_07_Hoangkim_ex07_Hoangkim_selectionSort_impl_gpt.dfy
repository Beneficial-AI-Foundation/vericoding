//Problem01
//a)

//b)
//Problem04

method FindMin(a: array<int>, lo: nat) returns (minIdx: nat)
    requires a != null && a.Length > 0 && lo < a.Length
    ensures lo <= minIdx < a.Length
    ensures forall x :: lo <= x < a.Length ==> a[minIdx] <= a[x]
{
  assume{:axiom} false;
}

//Problem02
ghost predicate sorted(a:seq<int>)
{
    forall i | 0 < i < |a| :: a[i-1] <= a[i]     
}

// <vc-helpers>
// no helpers needed
// </vc-helpers>

// <vc-spec>
method selectionSort(a: array<int>)
    modifies a
    //ensures multiset(a[..]) == multiset(old(a[..]))
    //ensures sorted(a[..])
// </vc-spec>
// <vc-code>
{
  if a != null {
    var i := 0;
    while i < a.Length
      invariant 0 <= i <= a.Length
      decreases a.Length - i
    {
      var m := i;
      var j := i + 1;
      while j < a.Length
        invariant i <= m < a.Length
        invariant i + 1 <= j <= a.Length
        decreases a.Length - j
      {
        if a[j] < a[m] {
          m := j;
        }
        j := j + 1;
      }
      if m != i {
        var tmp := a[i];
        a[i] := a[m];
        a[m] := tmp;
      }
      i := i + 1;
    }
  }
}
// </vc-code>

//Problem03