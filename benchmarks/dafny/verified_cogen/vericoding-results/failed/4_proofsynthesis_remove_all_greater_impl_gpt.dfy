// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Fixed sequence comprehension syntax and filtered by index */
function Filter(s: seq<int>, e: int): seq<int>
{
  seq i | 0 <= i && i < |s| && s[i] <= e :: s[i]
}

/* helper modified by LLM (iteration 4): Lemma proving membership properties of Filter */
lemma FilterProps(s: seq<int>, e: int)
  ensures forall x :: x in Filter(s, e) ==> x in s && x <= e
  ensures forall x :: x in s && x <= e ==> x in Filter(s, e)
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
{
  /* code modified by LLM (iteration 4): Construct filtered sequence and copy to result, preserving order */
  var f := Filter(v[..], e);
  var n := |f|;
  result := new int[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant result.Length == n
    invariant result[..i] == f[..i]
  {
    result[i] := f[i];
    i := i + 1;
  }
  // Use properties of Filter to discharge postconditions
  FilterProps(v[..], e);
}

// </vc-code>
