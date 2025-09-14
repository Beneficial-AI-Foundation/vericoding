// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Reverse (a : array<int>) returns (aRev : array<int>)
    ensures aRev.Length == a.Length
    ensures forall i : int :: 0 <= i < a.Length ==> a[i] == aRev[aRev.Length-i-1]
    ensures fresh(aRev)
// </vc-spec>
// <vc-code>
{
  aRev := new int[a.Length];
  var i := 0;
  while i < a.Length 
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> aRev[j] == a[a.Length-1-j]
  {
    aRev[i] := a[a.Length-1-i];
    i := i + 1;
  }
}
// </vc-code>
