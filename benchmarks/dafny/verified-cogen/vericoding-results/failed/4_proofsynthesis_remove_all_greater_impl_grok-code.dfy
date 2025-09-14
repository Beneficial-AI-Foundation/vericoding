// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method RemoveAllGreater(v: array<int>, e: int) returns (result: array<int>)

    requires 
        forall k1, k2 :: 0 <= k1 < k2 < v.Length ==> v[k1] != v[k2]

    ensures
        forall k :: 0 <= k < result.Length ==> result[k] <= e && result[k] in v[..]
    ensures
        forall k :: 0 <= k < v.Length && v[k] <= e ==> v[k] in result[..]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed duplicate local-variable name 'result' by removing 'var' since it's the return parameter */
{
  var count := 0;
  var i := 0;
  while i < v.Length
    invariant 0 <= i <= v.Length
    invariant 0 <= count <= i
  {
    if v[i] <= e {
      count := count + 1;
    }
    i := i + 1;
  }
  result := new int[count];
  i := 0;
  var pos := 0;
  while i < v.Length
    invariant 0 <= i <= v.Length
    invariant 0 <= pos <= count
    invariant pos == |set j | 0 <= j < i && v[j] <= e|
  {
    if v[i] <= e {
      result[pos] := v[i];
      pos := pos + 1;
    }
    i := i + 1;
  }
}
// </vc-code>
