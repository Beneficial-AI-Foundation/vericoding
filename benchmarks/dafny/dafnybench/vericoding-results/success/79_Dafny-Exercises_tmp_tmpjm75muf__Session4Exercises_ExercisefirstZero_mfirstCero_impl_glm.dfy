

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method mfirstCero(v:array<int>) returns (i:int)
ensures 0 <=i<=v.Length
ensures forall j:: 0<=j<i ==> v[j]!=0 
ensures i!=v.Length ==> v[i]==0
// </vc-spec>
// <vc-code>
{
  var idx := 0;
  while idx < v.Length && v[idx] != 0
    invariant 0 <= idx <= v.Length
    invariant forall j :: 0 <= j < idx ==> v[j] != 0
  {
    idx := idx + 1;
  }
  return idx;
}
// </vc-code>

