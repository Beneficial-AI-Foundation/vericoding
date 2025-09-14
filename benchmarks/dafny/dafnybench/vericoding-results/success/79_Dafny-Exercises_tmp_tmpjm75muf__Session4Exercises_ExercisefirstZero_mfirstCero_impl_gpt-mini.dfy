

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
  var k := 0;
  while k < v.Length && v[k] != 0
    invariant 0 <= k <= v.Length
    invariant forall j :: 0 <= j < k ==> v[j] != 0
    decreases v.Length - k
  {
    k := k + 1;
  }
  i := k;
}
// </vc-code>

