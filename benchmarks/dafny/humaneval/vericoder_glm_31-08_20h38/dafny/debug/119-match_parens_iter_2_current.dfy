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
  var total_s1 := CalcBal(s1, 0, |s1|, 0);

  // Check s1
  var i := 0;
  var current := 0;
  while i < |s1|
      invariant 0 <= i <= |s1|
      invariant current == CalcBal(s1, 0, i, 0)
  {
      if s1[i] == 0 {
          current := current + 1;
      } else {
          current := current - 1;
      }
      if current < 0 {
          return false;
      }
      i := i + 1;
  }

  // Check s2
  i := 0;
  current := total_s1;
  while i < |s2|
      invariant 0 <= i <= |s2|
      invariant current == total_s1 + CalcBal(s2, 0, i, 0)
  {
      if s2[i] == 0 {
          current := current + 1;
      } else {
          current := current - 1;
      }
      if current < 0 {
          return false;
      }
      i := i + 1;
  }

  return true;
}
// </vc-code>

