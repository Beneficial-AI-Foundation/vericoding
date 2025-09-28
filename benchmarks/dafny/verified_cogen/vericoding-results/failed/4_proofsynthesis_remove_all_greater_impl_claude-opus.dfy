// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Added lemma to prove uniqueness preservation in result array */
function CountLessOrEqual(v: array<int>, e: int, i: int): int
  requires 0 <= i <= v.Length
  reads v
  decreases i
{
  if i == 0 then 0
  else if v[i-1] <= e then CountLessOrEqual(v, e, i-1) + 1
  else CountLessOrEqual(v, e, i-1)
}

lemma CountLessOrEqualProperty(v: array<int>, e: int, i: int)
  requires 0 <= i < v.Length
  requires forall k1, k2 :: 0 <= k1 < k2 < v.Length ==> v[k1] != v[k2]
  ensures v[i] <= e ==> CountLessOrEqual(v, e, i + 1) == CountLessOrEqual(v, e, i) + 1
  ensures v[i] > e ==> CountLessOrEqual(v, e, i + 1) == CountLessOrEqual(v, e, i)
{
}
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
/* code modified by LLM (iteration 5): Fixed array bound check and invariant maintenance */
{
  var count := 0;
  var i := 0;
  while i < v.Length
    invariant 0 <= i <= v.Length
    invariant count == CountLessOrEqual(v, e, i)
  {
    if v[i] <= e {
      count := count + 1;
    }
    i := i + 1;
  }
  
  result := new int[count];
  var j := 0;
  var k := 0;
  
  while j < v.Length
    invariant 0 <= j <= v.Length
    invariant 0 <= k <= count
    invariant k == CountLessOrEqual(v, e, j)
    invariant forall m :: 0 <= m < k ==> result[m] <= e && result[m] in v[..]
    invariant forall m1, m2 :: 0 <= m1 < m2 < k ==> result[m1] != result[m2]
    invariant forall m :: 0 <= m < j && v[m] <= e ==> exists n :: 0 <= n < k && result[n] == v[m]
  {
    if v[j] <= e {
      CountLessOrEqualProperty(v, e, j);
      if k < count {
        result[k] := v[j];
        k := k + 1;
      }
    } else {
      CountLessOrEqualProperty(v, e, j);
    }
    j := j + 1;
  }
}
// </vc-code>
