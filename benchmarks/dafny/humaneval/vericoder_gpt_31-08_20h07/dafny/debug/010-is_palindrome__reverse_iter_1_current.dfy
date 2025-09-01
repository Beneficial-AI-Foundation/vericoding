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
  var j := 0;
  rev := "";
  while j < |str|
    invariant 0 <= j <= |str|
    invariant |rev| == j
    invariant forall k :: 0 <= k < j ==> rev[k] == str[j - 1 - k]
  {
    var c := str[j..j+1];
    var newRev := c + rev;
    var oldj := j;
    assert |c| == 1;

    // Prove relation for newRev with oldj
    assert forall k :: 0 <= k < oldj + 1 ==> newRev[k] == str[oldj - k] by {
      if k == 0 {
        assert newRev[0] == c[0];
        assert c[0] == str[oldj];
      } else {
        assert k >= |c|; // since |c| == 1 and k > 0
        assert newRev[k] == rev[k - |c|];
        assert 0 <= k - 1;
        assert k - 1 < oldj;
        assert rev[k - 1] == str[oldj - 1 - (k - 1)];
        assert newRev[k] == str[oldj - k];
      }
    };

    // Update rev and j
    rev := newRev;
    j := oldj + 1;

    // Maintain length invariant
    assert |rev| == j;

    // Maintain content invariant
    assert forall k :: 0 <= k < j ==> rev[k] == str[j - 1 - k] by {
      assert 0 <= k < oldj + 1;
      assert rev[k] == newRev[k];
      assert j - 1 - k == oldj - k;
    }
  }
}
// </vc-code>

