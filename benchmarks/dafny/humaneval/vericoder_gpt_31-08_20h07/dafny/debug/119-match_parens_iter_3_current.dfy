function CalcBal(s: seq<int>, i: int, j: int, acc: int) : int 
    requires 0 <= i <= j <= |s|
{
    if i == j then acc
    else (if s[j - 1] == 0 then 1 else -1) + CalcBal(s, i, j - 1, acc)
}

// <vc-helpers>
lemma NotForallImpliesExistsS1(s: seq<int>)
  ensures (! (forall i :: 0 <= i <= |s| ==> CalcBal(s, 0, i, 0) >= 0)) ==>
          (exists i :: 0 <= i <= |s| && CalcBal(s, 0, i, 0) < 0)
{
  if ! (forall i :: 0 <= i <= |s| ==> CalcBal(s, 0, i, 0) >= 0) {
    assert exists i :: 0 <= i <= |s| && !(CalcBal(s, 0, i, 0) >= 0);
    var k: int :| 0 <= k <= |s| && !(CalcBal(s, 0, k, 0) >= 0);
    assert CalcBal(s, 0, k, 0) < 0;
  }
}

lemma NotForallImpliesExistsS2(s1: seq<int>, s2: seq<int>)
  ensures (! (forall i :: 0 <= i <= |s2| ==> CalcBal(s1, 0, |s1|, 0) + CalcBal(s2, 0, i, 0) >= 0)) ==>
          (exists i :: 0 <= i <= |s2| && CalcBal(s1, 0, |s1|, 0) + CalcBal(s2, 0, i, 0) < 0)
{
  if ! (forall i :: 0 <= i <= |s2| ==> CalcBal(s1, 0, |s1|, 0) + CalcBal(s2, 0, i, 0) >= 0) {
    assert exists i :: 0 <= i <= |s2| && !(CalcBal(s1, 0, |s1|, 0) + CalcBal(s2, 0, i, 0) >= 0);
    var k: int :| 0 <= k <= |s2| && !(CalcBal(s1, 0, |s1|, 0) + CalcBal(s2, 0, k, 0) >= 0);
    assert CalcBal(s1, 0, |s1|, 0) + CalcBal(s2, 0, k, 0) < 0;
  }
}
// </vc-helpers>

// <vc-spec>
method checkFixed(s1: seq<int>, s2: seq<int>) returns (b: bool) 
    // pre-conditions-start
    requires forall i :: 0 <= i < |s1| ==> s1[i] == 0 || s1[i] == 1
    requires forall i :: 0 <= i < |s2| ==> s2[i] == 0 || s2[i] == 1
    // pre-conditions-end
    // post-conditions-start
    ensures b ==> forall i :: 0 <= i <= |s1| ==> CalcBal(s1, 0, i, 0) >= 0
    ensures b ==> forall i :: 0 <= i <= |s2| ==> CalcBal(s1, 0, |s1|, 0) + CalcBal(s2, 0, i, 0) >= 0
    ensures !b ==> (exists i :: 0 <= i <= |s1| && CalcBal(s1, 0, i, 0) < 0) || (exists i :: 0 <= i <= |s2| && CalcBal(s1, 0, |s1|, 0) + CalcBal(s2, 0, i, 0) < 0)
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var c1 := (forall i :: 0 <= i <= |s1| ==> CalcBal(s1, 0, i, 0) >= 0);
  var c2 := (forall i :: 0 <= i <= |s2| ==> CalcBal(s1, 0, |s1|, 0) + CalcBal(s2, 0, i, 0) >= 0);
  b := c1 && c2;
  if !b {
    if !c1 {
      NotForallImpliesExistsS1(s1);
      assert exists i :: 0 <= i <= |s1| && CalcBal(s1, 0, i, 0) < 0;
    } else {
      if !c2 {
        NotForallImpliesExistsS2(s1, s2);
        assert exists i :: 0 <= i <= |s2| && CalcBal(s1, 0, |s1|, 0) + CalcBal(s2, 0, i, 0) < 0;
      } else {
        assert b == c1 && c2;
        assert b;
        assert false;
      }
    }
  }
}
// </vc-code>

