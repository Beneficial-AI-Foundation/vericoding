function ThreeDistinct(s: string, i: int): bool
    requires 0 < i < |s| - 1
{
    (s[i - 1] != s[i]) && (s[i] != s[i + 1]) && (s[i - 1] != s[i + 1])
}
function Happy(s: string) : bool
{
    |s| >= 3 &&
    forall i :: 0 < i < |s| - 1 ==> ThreeDistinct(s, i)
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method IsHappy(s: string) returns (happy : bool)
    // post-conditions-start
    ensures happy <==> Happy(s)
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if |s| < 3 {
    happy := false;
  } else {
    var n := |s|;
    var i := 1;
    var allGood := true;
    while i < n - 1
      invariant 1 <= i <= n - 1
      invariant allGood <==> (forall j :: 0 < j < i ==> ThreeDistinct(s, j))
      decreases n - i
    {
      assert 0 < i < n - 1;
      assert ThreeDistinct(s, i) <==> ((s[i - 1] != s[i]) && (s[i] != s[i + 1]) && (s[i - 1] != s[i + 1]));
      allGood := allGood && (s[i - 1] != s[i]) && (s[i] != s[i + 1]) && (s[i - 1] != s[i + 1]);
      i := i + 1;
    }
    assert i == n - 1;
    happy := allGood;
  }
}
// </vc-code>

