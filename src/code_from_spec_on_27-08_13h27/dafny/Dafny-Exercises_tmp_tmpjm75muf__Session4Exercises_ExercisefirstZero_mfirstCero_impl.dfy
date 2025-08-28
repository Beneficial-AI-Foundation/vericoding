// <vc-helpers>
// No additional helpers or proofs needed for this implementation
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method mfirstCero(v:array<int>) returns (i:int)
ensures 0 <=i<=v.Length
ensures forall j:: 0<=j<i ==> v[j]!=0 
ensures i!=v.Length ==> v[i]==0
// </vc-spec>
// </vc-spec>

// <vc-code>
method firstCero(v: array<int>) returns (i: int)
  ensures 0 <= i <= v.Length
  ensures forall j :: 0 <= j < i ==> v[j] != 0
  ensures i != v.Length ==> v[i] == 0
{
  i := 0;
  while i < v.Length && v[i] != 0
    invariant 0 <= i <= v.Length
    invariant forall j :: 0 <= j < i ==> v[j] != 0
  {
    i := i + 1;
  }
}
// </vc-code>
