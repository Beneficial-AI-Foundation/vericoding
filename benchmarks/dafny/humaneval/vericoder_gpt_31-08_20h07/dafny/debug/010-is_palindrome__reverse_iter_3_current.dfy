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
// no helpers needed
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
  while 0 < i
    invariant 0 <= i <= |str|
    invariant |rev| == |str| - i
    invariant forall k :: 0 <= k < |rev| ==> rev[k] == str[|str| - 1 - k]
    decreases i
  {
    var oldI := i;
    var oldRev := rev;

    assert 0 < oldI <= |str|;
    assert 0 <= oldI - 1 < oldI <= |str|;

    var c := str[oldI - 1 .. oldI];
    assert |c| == 1;

    rev := oldRev + c;
    i := oldI - 1;

    assert |rev| == |oldRev| + 1;
    assert |rev| == |str| - i;

    assert forall k :: 0 <= k < |rev| ==> rev[k] == str[|str| - 1 - k] by {
      if k < |oldRev| {
        assert 0 <= k < |oldRev|;
        assert rev[k] == (oldRev + c)[k];
        assert (oldRev + c)[k] == oldRev[k];
        assert oldRev[k] == str[|str| - 1 - k];
      } else {
        assert |oldRev| <= k;
        assert k < |oldRev| + 1;
        assert k == |oldRev|;
        assert rev[k] == (oldRev + c)[|oldRev|];
        assert (oldRev + c)[|oldRev|] == c[0];
        assert c[0] == str[oldI - 1];
        assert |oldRev| == |str| - oldI;
        assert str[|str| - 1 - |oldRev|] == str[oldI - 1];
      }
    };
  }
}
// </vc-code>

