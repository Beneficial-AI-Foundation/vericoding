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
  var i := 0;
  while i < |str|
    invariant 0 <= i <= |str|
    invariant |rev| == i
    invariant forall k :: 0 <= k < i ==> rev[k] == str[|str| - 1 - k]
    decreases |str| - i
  {
    assert 0 <= i < |str|;
    var start := |str| - 1 - i;
    var stop := |str| - i;
    assert 0 <= start < stop <= |str|;
    var c := str[start..stop];
    assert |c| == 1;

    var prev := rev;
    var oldi := i;
    var newRev := prev + c;

    assert forall k :: 0 <= k < oldi ==> newRev[k] == prev[k] by {
      assert 0 <= k < |prev|;
    };

    assert oldi == |prev|;
    assert newRev[oldi] == c[0];
    assert c[0] == str[|str| - 1 - oldi];

    rev := newRev;
    i := oldi + 1;

    assert |rev| == i;

    assert forall k :: 0 <= k < i ==> rev[k] == str[|str| - 1 - k] by {
      if k < oldi {
        assert rev[k] == newRev[k];
        assert newRev[k] == prev[k];
        assert prev[k] == str[|str| - 1 - k];
      } else {
        assert k == oldi;
        assert rev[k] == newRev[oldi];
        assert newRev[oldi] == c[0];
        assert c[0] == str[|str| - 1 - oldi];
      }
    };
  }
}
// </vc-code>

