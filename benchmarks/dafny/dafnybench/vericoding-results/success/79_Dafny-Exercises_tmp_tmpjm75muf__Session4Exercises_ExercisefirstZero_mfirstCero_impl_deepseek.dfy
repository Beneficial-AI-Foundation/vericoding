

// <vc-helpers>
lemma FindFirstZeroLemma(v: array<int>, k: int)
  requires 0 <= k <= v.Length
  requires forall j :: 0 <= j < k ==> v[j] != 0
  ensures (k == v.Length || v[k] == 0) ==> 
          0 <= k <= v.Length && 
          (forall j :: 0 <= j < k ==> v[j] != 0) && 
          (k != v.Length ==> v[k] == 0)
{
}
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
  while i < v.Length && v[i] != 0
    invariant 0 <= i <= v.Length
    invariant forall j :: 0 <= j < i ==> v[j] != 0
  {
    i := i + 1;
  }
}
// </vc-code>

