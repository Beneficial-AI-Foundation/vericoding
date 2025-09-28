// <vc-preamble>
predicate IsSubrangeAt(main: seq<int>, sub: seq<int>, i: int)
{
    0 <= i && i + |sub| <= |main| && sub == main[i..i+|sub|]
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsSubArray(main: array<int>, sub: array<int>) returns (result: bool)
    ensures result == (exists k :: 0 <= k <= (main.Length - sub.Length) && IsSubrangeAt(main[..], sub[..], k))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): Fixed empty subarray case to properly verify postcondition */
  if sub.Length == 0 {
    assert IsSubrangeAt(main[..], sub[..], 0);
    return true;
  }
  if main.Length < sub.Length {
    return false;
  }
  
  var i := 0;
  while i <= main.Length - sub.Length
    invariant 0 <= i <= main.Length - sub.Length + 1
    invariant forall k :: 0 <= k < i ==> !IsSubrangeAt(main[..], sub[..], k)
  {
    var j := 0;
    var found := true;
    while j < sub.Length
      invariant 0 <= j <= sub.Length
      invariant found == (forall k :: 0 <= k < j ==> main[i + k] == sub[k])
    {
      if main[i + j] != sub[j] {
        found := false;
        break;
      }
      j := j + 1;
    }
    if found {
      assert j == sub.Length;
      assert forall k :: 0 <= k < sub.Length ==> main[i + k] == sub[k];
      assert sub[..] == main[i..i+sub.Length];
      assert IsSubrangeAt(main[..], sub[..], i);
      return true;
    }
    i := i + 1;
  }
  assert i == main.Length - sub.Length + 1;
  assert forall k :: 0 <= k <= main.Length - sub.Length ==> !IsSubrangeAt(main[..], sub[..], k);
  return false;
}
// </vc-code>
