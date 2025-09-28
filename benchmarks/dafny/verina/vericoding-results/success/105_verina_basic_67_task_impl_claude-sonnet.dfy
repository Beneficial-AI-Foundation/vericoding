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
  if |x| == 0 {
    result := true;
    return;
  }
  
  var i := 0;
  result := true;
  
  while i < |x| / 2
    invariant 0 <= i <= |x| / 2
    invariant result <==> (forall j :: 0 <= j < i ==> x[j] == x[|x| - 1 - j])
  {
    if x[i] != x[|x| - 1 - i] {
      result := false;
      return;
    }
    i := i + 1;
  }
}
// </vc-code>
