function CalcBal(s: seq<int>, i: int, j: int, acc: int) : int 
    requires 0 <= i <= j <= |s|
{
    if i == j then acc
    else (if s[j - 1] == 0 then 1 else -1) + CalcBal(s, i, j - 1, acc)
}

// <vc-helpers>

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
  var cum := 0;
  for i := 0 to |s1| 
    invariant cum == CalcBal(s1, 0, i, 0)
  {
    if i > 0 {
      if s1[i-1] == 0 {
        cum := cum + 1;
      } else {
        cum := cum - 1;
      }
    }
    if cum < 0 {
      return false;
    }
  }
  var total1 := cum;
  for i := 0 to |s2| 
    invariant cum == total1 + CalcBal(s2, 0, i, 0)
  {
    if i > 0 {
      if s2[i-1] == 0 {
        cum := cum + 1;
      } else {
        cum := cum - 1;
      }
    }
    if cum < 0 {
      return false;
    }
  }
  return true;
}
// </vc-code>

