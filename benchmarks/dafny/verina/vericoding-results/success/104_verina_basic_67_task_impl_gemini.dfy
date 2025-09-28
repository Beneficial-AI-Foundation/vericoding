// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsPalindrome(x: seq<char>) returns (result: bool)
    ensures
        result <==> (forall i :: 0 <= i < |x| ==> x[i] == x[|x| - 1 - i])
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < |x| / 2
    invariant 0 <= i <= |x| / 2
    invariant forall k :: 0 <= k < i ==> x[k] == x[|x| - 1 - k]
  {
    if x[i] != x[|x| - 1 - i] {
      result := false;
      return;
    }
    i := i + 1;
  }
  result := true;
}
// </vc-code>
