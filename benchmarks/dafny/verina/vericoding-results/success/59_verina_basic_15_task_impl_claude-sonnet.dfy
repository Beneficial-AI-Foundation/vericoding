// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method ContainsConsecutiveNumbers(a: seq<int>) returns (result: bool)
    ensures
        result <==> exists i :: 0 <= i < |a| - 1 && a[i] + 1 == a[i + 1]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): fixed array bounds in loop invariant */
  result := false;
  var i := 0;
  while i < |a| - 1
    invariant 0 <= i <= |a|
    invariant !result ==> forall j :: 0 <= j < i && j < |a| - 1 ==> a[j] + 1 != a[j + 1]
  {
    if a[i] + 1 == a[i + 1] {
      result := true;
      return;
    }
    i := i + 1;
  }
}
// </vc-code>
