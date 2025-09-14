predicate ValidInput(s: string)
{
    |s| >= 1 && |s| <= 100 && forall i :: 0 <= i < |s| ==> 'a' <= s[i] <= 'z'
}

predicate ValidOutput(s: string, result: string)
{
    |result| == |s| && forall i :: 0 <= i < |result| ==> result[i] == 'x'
}

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solve(s: string) returns (result: string)
    requires ValidInput(s)
    ensures ValidOutput(s, result)
// </vc-spec>
// <vc-code>
{
  result := "";
  var i := 0;
  while i < |s|
    invariant 0 <= i <= |s|
    invariant |result| == i
    invariant forall j :: 0 <= j < |result| ==> result[j] == 'x'
    decreases |s| - i
  {
    var prev := result;
    result := result + "x";
    i := i + 1;

    assert |result| == |prev| + 1;

    assert forall j :: 0 <= j < |result| ==> result[j] == 'x' by
    {
      forall j | 0 <= j < |result|
        ensures result[j] == 'x'
      {
        if j < |prev| {
          assert result[j] == prev[j];
        } else {
          assert j == |prev|;
          assert result[j] == "x"[j - |prev|];
          assert j - |prev| == 0;
          assert "x"[0] == 'x';
        }
      }
    }

    assert |result| == i;
  }
  return;
}
// </vc-code>

