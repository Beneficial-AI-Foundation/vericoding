// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): defines ConsecutiveAt predicate safely */
function {:inline} ConsecutiveAt(a: seq<int>, i: int): bool {
  0 <= i && i < |a| - 1 && a[i] + 1 == a[i + 1]
}
// </vc-helpers>

// <vc-spec>
method ContainsConsecutiveNumbers(a: seq<int>) returns (result: bool)
    ensures
        result <==> exists i :: 0 <= i < |a| - 1 && a[i] + 1 == a[i + 1]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): iterate through sequence, set result if consecutive pair found */
  var i := 0;
  result := false;
  while i < |a| - 1
    invariant 0 <= i && i <= |a|
    invariant result <==> (exists j :: 0 <= j && j < i && j + 1 < |a| && a[j] + 1 == a[j + 1])
  {
    if ConsecutiveAt(a, i) {
      result := true;
      return;
    }
    i := i + 1;
  }
}
// </vc-code>
