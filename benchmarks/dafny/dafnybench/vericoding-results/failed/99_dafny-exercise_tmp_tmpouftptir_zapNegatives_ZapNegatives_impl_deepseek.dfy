

// <vc-helpers>
lemma ZapNegativesLemma(a: array<int>, j: int)
  requires 0 <= j <= a.Length
  ensures forall i :: 0 <= i < j ==> (if old(a[i]) < 0 then a[i] == 0 else a[i] == old(a[i]))
  ensures forall i :: j <= i < a.Length ==> a[i] == old(a[i])
  ensures a.Length == old(a.Length)
  decreases a.Length - j
{
  if j < a.Length {
    // Recursive case: prove for j+1
    ghost var old_vals := new int[a.Length];
    forall k | 0 <= k < a.Length {
      old_vals[k] := a[k];
    }
    
    if a[j] < 0 {
      a[j] := 0;
    }
    
    ZapNegativesLemma(a, j + 1);
    
    // Restore array state for ghost lemma
    forall k | 0 <= k < a.Length {
      a[k] := old_vals[k];
    }
  }
}
// </vc-helpers>

// <vc-spec>
method ZapNegatives(a: array<int>) 
modifies a
ensures forall i :: 0 <= i < a.Length ==> if old(a[i]) < 0 then a[i] == 0 
                                            else a[i] == old(a[i])
ensures a.Length == old(a).Length
// </vc-spec>
// <vc-code>
{
  var index := 0;
  while index < a.Length
    invariant 0 <= index <= a.Length
    invariant forall i :: 0 <= i < index ==> (if old(a[i]) < 0 then a[i] == 0 else a[i] == old(a[i]))
    invariant forall i :: index <= i < a.Length ==> a[i] == old(a[i])
    invariant a.Length == old(a.Length)
  {
    if a[index] < 0 {
      a[index] := 0;
    }
    index := index + 1;
  }
}
// </vc-code>

