// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
lemma NoOpLemma() {
}

// </vc-helpers>

// <vc-spec>
method IsPalindrome(x: seq<char>) returns (result: bool)
    ensures
        result <==> (forall i :: 0 <= i < |x| ==> x[i] == x[|x| - 1 - i])
// </vc-spec>
// <vc-code>
{
  var n := |x|;
  var i := 0;
  var ok := true;
  while i < n
    invariant 0 <= i <= n
    invariant ok ==> (forall j :: 0 <= j < i ==> x[j] == x[n - 1 - j])
    invariant (!ok) ==> (exists j :: 0 <= j < i && x[j] != x[n - 1 - j])
    decreases n - i
  {
    if x[i] != x[n - 1 - i] {
      ok := false;
    }
    i := i + 1;
  }
  if (forall j | 0 <= j < n :: x[j] == x[n - 1 - j]) {
    assert ok;
  }
  result := ok;
}
// </vc-code>
