// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): added function to count elements <= e in a prefix */
function CountLE(v: array<int>, e: int, hi: int): int
    requires 0 <= hi <= v.Length
    reads v
{
    if hi == 0 then 0 else CountLE(v, e, hi-1) + (if v[hi-1] <= e then 1 else 0)
}
// </vc-helpers>

// <vc-spec>
method RemoveAllGreater(v: array<int>, e: int) returns (result: array<int>)
    requires 
        forall k1, k2 :: 0 <= k1 < k2 < v.Length ==> v[k1] != v[k2]
    ensures
        forall k :: 0 <= k < result.Length ==> result[k] <= e && (exists j :: 0 <= j < v.Length && v[j] == result[k])
    ensures
        forall k :: 0 <= k < v.Length && v[k] <= e ==> (exists j :: 0 <= j < result.Length && result[j] == v[k])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): added loop invariants to prove postconditions */
  var count := 0;
  for i := 0 to v.Length
    invariant 0 <= count <= i
    invariant count == CountLE(v, e, i)
  {
    if v[i] <= e {
      count := count + 1;
    }
  }

  result := new int[count];
  var idx := 0;
  for i := 0 to v.Length
    invariant 0 <= idx <= count
    invariant idx == CountLE(v, e, i)
    invariant forall k :: 0 <= k < idx ==> result[k] <= e && (exists j :: 0 <= j < i && v[j] == result[k])
    invariant forall j :: 0 <= j < i && v[j] <= e ==> (exists k :: 0 <= k < idx && result[k] == v[j])
  {
    if v[i] <= e {
      result[idx] := v[i];
      idx := idx + 1;
    }
  }
}
// </vc-code>
