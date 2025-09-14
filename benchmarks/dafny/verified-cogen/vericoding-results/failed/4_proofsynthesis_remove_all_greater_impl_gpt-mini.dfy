// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): count and splitting lemmas for CountLE, and prefix element lemma */
function CountLE(s: seq<int>, e: int): nat { if |s| == 0 then 0 else CountLE(s[1..], e) + (if s[0] <= e then 1 else 0) }

lemma CountLESplit(s: seq<int>, e: int, i: int)
  requires 0 <= i <= |s|
  ensures CountLE(s, e) == CountLE(s[0..i], e) + CountLE(s[i..], e)
  decreases i
{
  if i == 0 {
  } else {
    var head := s[0];
    var tail := s[1..];
    assert s[0..i] == [head] + tail[0..i - 1];
    assert s[i..] == tail[i - 1..];
    CountLESplit(tail, e, i - 1);
    assert CountLE([head] + tail, e) == CountLE(tail, e) + (if head <= e then 1 else 0);
    assert CountLE([head] + tail[0..i - 1], e) == CountLE(tail[0..i - 1], e) + (if head <= e then 1 else 0);
    assert CountLE(tail, e) == CountLE(tail[0..i - 1], e) + CountLE(tail[i - 1..], e);
    assert CountLE(s, e) == CountLE(s[0..i], e) + CountLE(s[i..], e);
  }
}

lemma CountLEAppendIndex(s: seq<int>, e: int, i: int)
  requires 0 <= i < |s|
  ensures CountLE(s[0..i+1], e) == CountLE(s[0..i], e) + (if s[i] <= e then 1 else 0)
{
  CountLESplit(s[0..i+1], e, i);
  assert (s[0..i+1])[0..i] == s[0..i];
  assert (s[0..i+1])[i..] == s[i..i+1];
  assert CountLE(s[i..i+1], e) == (if s[i] <= e then 1 else 0);
  assert CountLE(s[0..i+1], e) == CountLE(s[0..i], e) + CountLE(s[i..i+1], e);
}

lemma ElementInPrefix(s: seq<int>, i: int)
  requires 0 <= i < |s|
  ensures s[i] in s[0..i+1]
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
  /* code modified by LLM (iteration 5): filter array into new array preserving elements <= e, using CountLE lemmas */
  var s := v[..];
  result := new int[CountLE(s, e)];
  var i := 0;
  var j := 0;
  while i < v.Length
    invariant 0 <= i <= v.Length
    invariant 0 <= j <= result.Length
    invariant j == CountLE(s[0..i], e)
    invariant forall t :: 0 <= t < j ==> result[t] <= e && result[t] in s[0..i]
    invariant forall u :: 0 <= u < i && s[u] <= e ==> exists k :: 0 <= k < j && result[k] == s[u]
  {
    CountLEAppendIndex(s, e, i);
    if s[i] <= e {
      assert j == CountLE(s[0..i], e);
      assert CountLE(s[0..i+1], e) == CountLE(s[0..i], e) + 1;
      assert CountLE(s[0..i+1], e) == j + 1;
      result[j] := s[i];
      assert result[j] == s[i];
      ElementInPrefix(s, i);
      assert s[i] in s[0..i+1];
      j := j + 1;
    }
    i := i + 1;
  }
  CountLESplit(s, e, v.Length);
  assert j == CountLE(s, e);
}

// </vc-code>
