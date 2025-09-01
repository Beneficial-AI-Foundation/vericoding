function is_palindrome(s : string) : bool {
    forall k :: 0 <= k < |s| ==> s[k] == s[|s| - 1 - k]
}
function starts_with(result : string, s : string) : bool {
    |result| >= |s| && forall k :: 0 <= k < |s| ==> result[k] == s[k]
}
method make_palindrome(s: string) returns (result: string)
    // post-conditions-start
    ensures |result| <= 2 * |s|
    ensures is_palindrome(result)
    ensures starts_with(result, s)
    // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma Lemma_AppendLastMaintainsReverse(str: string, oldRev: string, i: int)
  requires 0 < i <= |str|
  requires forall k :: 0 <= k < |oldRev| ==> oldRev[k] == str[|str| - 1 - k]
  requires |oldRev| == |str| - i
  ensures forall k :: 0 <= k < |oldRev| + 1 ==> (oldRev + str[i - 1 .. i])[k] == str[|str| - 1 - k]
{
  var c := str[i - 1 .. i];
  assert c == str[i - 1 .. i];
  forall k | 0 <= k < |oldRev| + 1
    ensures (oldRev + c)[k] == str[|str| - 1 - k]
  {
    if k < |oldRev| {
      assert (oldRev + c)[k] == oldRev[k];
      assert oldRev[k] == str[|str| - 1 - k];
    } else {
      assert k == |oldRev|;
      assert (oldRev + c)[|oldRev|] == c[0];
      assert c[0] == str[i - 1];
      assert |str| - 1 - k == |str| - 1 - |oldRev|;
      assert |str| - 1 - |oldRev| == i - 1;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method reverse(str: string) returns (rev: string)
    // post-conditions-start
    ensures |rev| == |str|
    ensures forall k :: 0 <= k < |str| ==> rev[k] == str[|str| - 1 - k]
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  rev := "";
  var i := |str|;
  while i > 0
    invariant 0 <= i <= |str|
    invariant |rev| == |str| - i
    invariant forall k :: 0 <= k < |rev| ==> rev[k] == str[|str| - 1 - k]
    decreases i
  {
    Lemma_AppendLastMaintainsReverse(str, rev, i);
    rev := rev + str[i - 1 .. i];
    i := i - 1;
  }
}
// </vc-code>

