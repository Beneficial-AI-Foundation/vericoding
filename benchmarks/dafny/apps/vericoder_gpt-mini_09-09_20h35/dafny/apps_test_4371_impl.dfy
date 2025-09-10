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
    invariant 0 <= i <= n - 2
    invariant best >= 0
    invariant forall j :: 0 <= j < i && j <= n - 3 ==> best <= abs(753 - StringToInt(S[j..j+3]))
    invariant i == 0 || (exists j :: 0 <= j < i && j <= n - 3 && best == abs(753 - StringToInt(S[j..j+3])))
    decreases n - i
  {
    var oldv := best;
    // establish substring preconditions for S[i..i+3]
    assert 0 <= i && i <= n - 3;
    assert '1' <= S[i] <= '9';
    assert '1' <= S[i+1] <= '9';
    assert '1' <= S[i+2] <= '9';
    var cur := StringToInt(S[i..i+3]);
    var d := abs(753 - cur);
    if d < oldv {
      best := d;
      // previous invariant (with oldv) holds for indices < i
      assert forall j :: 0 <= j < i && j <= n - 3 ==> oldv <= abs(753 - StringToInt(S[j..j+3]));
      // since best < oldv, best <= those distances as well
      assert forall j :: 0 <= j < i && j <= n - 3 ==> best <= abs(753 - StringToInt(S[j..j+3]));
      // best equals distance at index i
      assert best == abs(753 - StringToInt(S[i..i+3]));
      // hence there exists a j < i+1 (namely i) with the required property
      assert 0 <= i < i+1 && i <= n - 3;
      assert exists j :: 0 <= j < i+1 && j <= n - 3 && best == abs(753 - StringToInt(S[j..j+3]));
      // show the forall for i+1
      assert forall j :: 0 <= j < i+1 && j <= n - 3 ==> best <= abs(753 - StringToInt(S[j..j+3]));
    } else {
      // oldv == best and oldv <= d, so best <= distance at i
      assert oldv == best;
      assert oldv <= d;
      assert best <= d;
      // use invariant for j < i and the fact best <= d for j == i to get the forall for i+1
      assert forall j :: 0 <= j < i && j <= n - 3 ==> best <= abs(753 - StringToInt(S[j..j+3]));
      assert best <= abs(753 - StringToInt(S[i..i+3]));
      assert forall j :: 0 <= j < i+1 && j <= n - 3 ==> best <= abs(753 - StringToInt(S[j..j+3]));
      // existence: either previous existence (if i>0) or now (if i==0 and best equals current)
      if i == 0 {
        // i == 0, must show existence for range 0..0 (i.e., index 0)
        assert exists j :: 0 <= j < i+1 && j <= n - 3 && best == abs(753 - StringToInt(S[j..j+3]));
      } else {
        // i > 0: use previous existence for some j < i
        assert (exists j :: 0 <= j < i && j <= n - 3 && best == abs(753 - StringToInt(S[j..j+3])));
        // that same j witnesses existence for range 0..i
        assert exists j :: 0 <= j < i+1 && j <= n - 3 && best == abs(753 - StringToInt(S[j..j+3]));
      }
    }
    i := i + 1;
  }
  result := best;
}
// </vc-code>

