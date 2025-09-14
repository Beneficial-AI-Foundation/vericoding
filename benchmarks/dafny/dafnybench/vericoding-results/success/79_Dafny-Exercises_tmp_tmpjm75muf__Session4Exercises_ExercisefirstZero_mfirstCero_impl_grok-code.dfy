

// <vc-helpers>
// This section is empty and no updates are needed.
// </vc-helpers>

// <vc-spec>
method mfirstCero(v:array<int>) returns (i:int)
ensures 0 <=i<=v.Length
ensures forall j:: 0<=j<i ==> v[j]!=0 
ensures i!=v.Length ==> v[i]==0
// </vc-spec>
// <vc-code>
{
  i := 0;
  while i < v.Length
    invariant 0 <= i <= v.Length
    invariant forall j :: 0 <= j < i ==> v[j] != 0
  {
    if v[i] == 0 {
      return i;
    }
    i := i + 1;
  }
  return i;
}
// </vc-code>

