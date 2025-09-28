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
{
  var s: seq<int> := [];
  var i: int := 0;
  while i < v.Length
    invariant 0 <= i <= v.Length
    invariant forall k :: 0 <= k < i && v[k] <= e ==> v[k] in s
    invariant forall x :: x in s ==> x in v[..i] && x <= e
  {
    if v[i] <= e {
      s := s + [v[i]];
    }
    i := i + 1;
  }
  result := new int[|s|](j => s[j]);
}
// </vc-code>
