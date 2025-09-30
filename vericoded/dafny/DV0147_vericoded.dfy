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
  result := true;
  var n := |x|;
  var i := 0;
  while i < n / 2
    invariant 0 <= i <= n / 2
    invariant result <==> (forall j :: 0 <= j < i ==> x[j] == x[n - 1 - j])
  {
    if x[i] != x[n - 1 - i] {
      result := false;
      break;
    }
    i := i + 1;
  }
}
// </vc-code>
