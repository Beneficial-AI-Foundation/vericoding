// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added precondition to ensure index bounds */
function ComparePair(x: seq<char>, i: int): bool
    requires 0 <= i < |x|
{
    x[i] == x[|x|-1-i]
}
// </vc-helpers>

// <vc-spec>
method IsPalindrome(x: seq<char>) returns (result: bool)
    ensures
        result <==> (forall i :: 0 <= i < |x| ==> x[i] == x[|x| - 1 - i])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): changed to while loop with stronger invariant to cover entire sequence */
  var n := |x|;
  var i := 0;
  while i < n - i
      invariant forall j :: 0 <= j < n ==> (j < i || j >= n - i) ==> x[j] == x[n-1-j]
  {
      if !ComparePair(x, i) {
          return false;
      }
      i := i + 1;
  }
  return true;
}
// </vc-code>
