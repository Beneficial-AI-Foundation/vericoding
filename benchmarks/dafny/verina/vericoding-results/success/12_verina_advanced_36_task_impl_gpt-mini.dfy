// <vc-preamble>
function CountMatches(xs: seq<nat>, x: nat): nat
    decreases |xs|
{
    if |xs| == 0 then
        0
    else
        var firstMatch: nat := if xs[0] == x then 1 else 0;
        firstMatch + CountMatches(xs[1..], x)
}
// </vc-preamble>

// <vc-helpers>
lemma CountMatches_Pos_ExistsIndex(xs: seq<nat>, x: nat)
  decreases |xs|
  ensures CountMatches(xs, x) > 0 ==> exists i :: 0 <= i < |xs| && xs[i] == x
{
  if |xs| == 0 {
    // vacuously true
  } else if xs[0] == x {
    if CountMatches(xs, x) > 0 {
      assert exists i :: 0 <= i < |xs| && xs[i] == x;
    }
  } else {
    CountMatches_Pos_ExistsIndex(xs[1..], x);
    if CountMatches(xs, x) > 0 {
      assert CountMatches(xs[1..], x) > 0;
      var k :| 0 <= k < |xs[1..]| && xs[1..][k] == x;
      var i := k + 1;
      assert 0 <= i < |xs|;
      assert xs[i] == x;
      assert exists j :: 0 <= j < |xs| && xs[j] == x;
    }
  }
}

lemma ExistsMajorityImpliesElementPresent(xs: seq<nat>)
  requires exists x :: CountMatches(xs, x) > |xs| / 2
  ensures exists i :: 0 <= i < |xs| && CountMatches(xs, xs[i]) > |xs| / 2
{
  var x :| CountMatches(xs, x) > |xs| / 2;
  CountMatches_Pos_ExistsIndex(xs, x);
  var j :| 0 <= j < |xs| && xs[j] == x;
  assert CountMatches(xs, xs[j]) == CountMatches(xs, x);
  assert CountMatches(xs, xs[j]) > |xs| / 2;
  assert exists i :: 0 <= i < |xs| && CountMatches(xs, xs[i]) > |xs| / 2;
}
// </vc-helpers>

// <vc-spec>
method MajorityElement(xs: array<nat>) returns (result: nat)
    requires 
        xs.Length > 0
    requires
        exists x: nat :: CountMatches(xs[..], x) > xs.Length / 2
    ensures
        CountMatches(xs[..], result) > xs.Length / 2
// </vc-spec>
// <vc-code>
{
  var n := xs.Length;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
  {
    if CountMatches(xs[..], xs[i]) > n / 2 {
      result := xs[i];
      return;
    }
    i := i + 1;
  }
  // Constructively pick the majority element (guaranteed by the precondition)
  ExistsMajorityImpliesElementPresent(xs[..]);
  var j :| 0 <= j < n && CountMatches(xs[..], xs[j]) > n / 2;
  result := xs[j];
}
// </vc-code>
