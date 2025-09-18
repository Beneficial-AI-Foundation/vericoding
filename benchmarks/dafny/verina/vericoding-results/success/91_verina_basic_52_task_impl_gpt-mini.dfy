// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): prove multiset preserved when inserting element at position */
lemma Multiset_AddElementAt(s: seq<int>, x: int, pos: int)
  requires 0 <= pos <= |s|
  ensures multiset(s[..pos] + [x] + s[pos..]) == multiset(s) + multiset([x])
{
  // s == s[..pos] + s[pos..]
  assert s == s[..pos] + s[pos..];
  // multiset(s) == multiset(s[..pos]) + multiset(s[pos..])
  assert multiset(s) == multiset(s[..pos]) + multiset(s[pos..]);
  // concatenation with [x]
  assert multiset(s[..pos] + [x] + s[pos..]) == multiset(s[..pos]) + multiset([x]) + multiset(s[pos..]);
  // combine to get desired equality
  assert multiset(s) + multiset([x]) == multiset(s[..pos]) + multiset([x]) + multiset(s[pos..]);
}

// </vc-helpers>

// <vc-spec>
method BubbleSort(a: seq<int>) returns (result: seq<int>)
    ensures |result| == |a|
    ensures forall i, j :: 0 <= i < j < |result| ==> result[i] <= result[j]
    ensures multiset(a) == multiset(result)
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 3): implement insertion-based stable accumulation to result with proper bounds invariants */
{
  result := [];
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant |result| == i
    invariant forall p, q :: 0 <= p < q < |result| ==> result[p] <= result[q]
    invariant multiset(result) + multiset(a[i..]) == multiset(a)
    decreases |a| - i
  {
    var x := a[i];
    var oldres := result;
    var pos := 0;
    while pos < |oldres| && oldres[pos] < x
      invariant 0 <= pos <= |oldres|
      invariant forall j :: 0 <= j < pos ==> oldres[j] < x
      decreases |oldres| - pos
    {
      pos := pos + 1;
    }
    if pos < |oldres| { assert oldres[pos] >= x; }
    assert a[i..] == [x] + a[i+1..];
    Multiset_AddElementAt(oldres, x, pos);
    result := oldres[..pos] + [x] + oldres[pos..];
    assert multiset(result) == multiset(oldres) + multiset([x]);
    assert multiset(a[i..]) == multiset([x]) + multiset(a[i+1..]);
    assert multiset(result) + multiset(a[i+1..]) == multiset(a);
    i := i + 1;
  }
  assert i == |a|;
  assert |result| == |a|;
}

// </vc-code>
