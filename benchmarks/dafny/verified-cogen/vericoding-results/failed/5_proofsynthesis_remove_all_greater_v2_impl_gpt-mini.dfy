// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): sequence count function */
function SeqCountLE(s: seq<int>, e: int): nat
  decreases |s|
{
  if |s| == 0 then 0 else SeqCountLE(s[1..], e) + (if s[0] <= e then 1 else 0)
}

/* helper modified by LLM (iteration 2): append lemma */
lemma SeqCountLE_Append(s: seq<int>, x: int, e: int)
  ensures SeqCountLE(s + [x], e) == SeqCountLE(s, e) + (if x <= e then 1 else 0)
{
  if |s| == 0 {
    assert SeqCountLE([x], e) == 0 + (if x <= e then 1 else 0);
    return;
  } else {
    var tail := s[1..];
    // Inductive step on the tail
    SeqCountLE_Append(tail, x, e);
    // Unfold definitions for head/tail decomposition
    assert SeqCountLE(s, e) == SeqCountLE(tail, e) + (if s[0] <= e then 1 else 0);
    assert SeqCountLE(s + [x], e) == SeqCountLE(tail + [x], e) + (if s[0] <= e then 1 else 0);
    assert SeqCountLE(tail + [x], e) == SeqCountLE(tail, e) + (if x <= e then 1 else 0);
    return;
  }
}

/* helper modified by LLM (iteration 2): prefix monotonicity lemma */
lemma SeqCountLE_Prefix(s: seq<int>, t: seq<int>, e: int)
  requires |s| <= |t|
  requires s == t[..|s|]
  ensures SeqCountLE(s, e) <= SeqCountLE(t, e)
{
  if |s| == 0 {
    return;
  }
  var tailS := s[1..];
  var tailT := t[1..];
  SeqCountLE_Prefix(tailS, tailT, e);
  assert SeqCountLE(s, e) == SeqCountLE(tailS, e) + (if s[0] <= e then 1 else 0);
  assert SeqCountLE(t, e) == SeqCountLE(tailT, e) + (if t[0] <= e then 1 else 0);
  assert s[0] == t[0];
  // combine inductive hypothesis and equal flags
  assert SeqCountLE(tailS, e) + (if s[0] <= e then 1 else 0) <= SeqCountLE(tailT, e) + (if t[0] <= e then 1 else 0);
  return;
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
  /* code modified by LLM (iteration 2): implement RemoveAllGreater using helpers */
  var len := SeqCountLE(v[..], e);
  result := new int[len];
  var i := 0;
  var j := 0;
  while i < v.Length
    invariant 0 <= i <= v.Length
    invariant 0 <= j <= len
    invariant j == SeqCountLE(v[..i], e)
    invariant forall k :: 0 <= k < j ==> result[k] <= e && (exists idx :: 0 <= idx < v.Length && v[idx] == result[k])
    invariant forall k :: 0 <= k < i && v[k] <= e ==> (exists idx :: 0 <= idx < j && result[idx] == v[k])
    invariant forall k :: 0 <= k < j ==> (exists idx :: 0 <= idx < i && result[k] == v[idx])
    decreases v.Length - i
  {
    if v[i] <= e {
      // show there is room to write: SeqCountLE(v[..i+1],e) = SeqCountLE(v[..i],e) + 1 and <= len
      SeqCountLE_Append(v[..i], v[i], e);
      SeqCountLE_Prefix(v[..i+1], v[..], e);
      assert SeqCountLE(v[..i+1], e) == SeqCountLE(v[..i], e) + 1;
      assert SeqCountLE(v[..i+1], e) <= SeqCountLE(v[..], e);
      assert SeqCountLE(v[..i], e) < len;
      result[j] := v[i];
      j := j + 1;
    }
    i := i + 1;
  }
  assert j == len;
}

// </vc-code>
