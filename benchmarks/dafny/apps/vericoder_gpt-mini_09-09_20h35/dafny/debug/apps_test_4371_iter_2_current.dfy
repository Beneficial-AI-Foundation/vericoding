predicate ValidInput(S: string)
{
    |S| >= 3 && forall i :: 0 <= i < |S| ==> '1' <= S[i] <= '9'
}

function StringToInt(s: string): int
    requires |s| == 3
    requires forall i :: 0 <= i < |s| ==> '1' <= s[i] <= '9'
    ensures StringToInt(s) >= 111
    ensures StringToInt(s) <= 999
{
    100 * ((s[0] as int) - ('0' as int)) + 
    10 * ((s[1] as int) - ('0' as int)) + 
    ((s[2] as int) - ('0' as int))
}

function abs(x: int): int
    ensures abs(x) >= 0
    ensures abs(x) == x || abs(x) == -x
{
    if x >= 0 then x else -x
}

predicate IsMinimumDifference(S: string, result: int)
    requires ValidInput(S)
{
    result >= 0 &&
    (exists i :: 0 <= i <= |S| - 3 && result == abs(753 - StringToInt(S[i..i+3]))) &&
    (forall i :: 0 <= i <= |S| - 3 ==> result <= abs(753 - StringToInt(S[i..i+3])))
}

// <vc-helpers>
// No auxiliary helpers required for verification.
// </vc-helpers>

// <vc-spec>
method solve(S: string) returns (result: int)
    requires ValidInput(S)
    ensures IsMinimumDifference(S, result)
// </vc-spec>
// <vc-code>
{
  var n := |S|;
  var i := 0;
  var best := 1000;
  while i <= n - 3
    invariant 0 <= i <= n
    invariant best >= 0
    invariant forall j :: 0 <= j < i ==> best <= abs(753 - StringToInt(S[j..j+3]))
    invariant i == 0 || (exists j :: 0 <= j < i && best == abs(753 - StringToInt(S[j..j+3])))
    decreases n - i
  {
    var oldv := best;
    var cur := StringToInt(S[i..i+3]);
    var d := abs(753 - cur);
    if d < oldv {
      best := d;
      assert forall j :: 0 <= j < i ==> best <= abs(753 - StringToInt(S[j..j+3]));
      assert exists j :: 0 <= j < i+1 && best == abs(753 - StringToInt(S[j..j+3]));
    } else {
      assert forall j :: 0 <= j < i+1 ==> best <= abs(753 - StringToInt(S[j..j+3]));
      assert i == 0 || (exists j :: 0 <= j < i+1 && best == abs(753 - StringToInt(S[j..j+3])));
    }
    i := i + 1;
  }
  result := best;
}
// </vc-code>

