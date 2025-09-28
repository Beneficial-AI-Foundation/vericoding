predicate ValidInput(n: int, s: string) {
    n == |s| && n >= 1
}

function CountDistinctChars(s: string): int {
    |set c | c in s|
}

// <vc-helpers>
lemma CountDistinctUpper(s: string)
  ensures CountDistinctChars(s) <= |s|
{
  if |s| == 0 {
    assert CountDistinctChars(s) == 0;
  } else {
    var s0 := s[..|s|-1];
    CountDistinctUpper(s0);
    var ch := s[|s|-1];
    var S0 := set c | c in s0;
    var SAll := set c | c in s;
    // membership decomposition: x in s iff x in s0 or x == ch
    assert forall x :: x in SAll <==> (x in S0 || x == ch);
    if ch in S0 {
      assert forall x :: x in SAll <==> x in S0;
      assert SAll == S0;
      assert CountDistinctChars(s) == CountDistinctChars(s0);
      assert CountDistinctChars(s) <= |s0|;
      assert |s0| < |s|;
      assert CountDistinctChars(s) <= |s|;
    } else {
      assert SAll == S0 + {ch};
      assert CountDistinctChars(s) == CountDistinctChars(s0) + 1;
      assert CountDistinctChars(s0) + 1 <= |s0| + 1;
      assert |s0| + 1 == |s|;
      assert CountDistinctChars(s) <= |s|;
    }
  }
}

lemma CountDistinctLower(s: string)
  requires |s| >= 1
  ensures CountDistinctChars(s) >= 1
{
  var c := s[0];
  var S := set ch | ch in s;
  assert c in S;
  assert CountDistinctChars(s) >= 1;
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, s: string) returns (result: int)
    requires ValidInput(n, s)
    ensures n > 26 ==> result == -1
    ensures n <= 26 ==> result >= 0 && result < n
    ensures n <= 26 ==> result == |s| - CountDistinctChars(s)
// </vc-spec>
// <vc-code>
{
  if n > 26 {
    result := -1;
  } else {
    CountDistinctUpper(s);
    CountDistinctLower(s);
    var d := CountDistinctChars(s);
    result := n - d;
  }
}
// </vc-code>

