function CalcBal(s: seq<int>, i: int, j: int, acc: int) : int 
    requires 0 <= i <= j <= |s|
{
    if i == j then acc
    else (if s[j - 1] == 0 then 1 else -1) + CalcBal(s, i, j - 1, acc)
}

// <vc-helpers>
lemma CalcBal_step(s: seq<int>, k: int)
  requires 0 <= k < |s|
  ensures CalcBal(s, 0, k+1, 0) == (if s[k] == 0 then 1 else -1) + CalcBal(s, 0, k, 0)
{
  // Follows directly from the definition of CalcBal
  assert CalcBal(s, 0, k+1, 0) == (if s[k] == 0 then 1 else -1) + CalcBal(s, 0, k, 0);
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
  var k := 0;
  var bal := 0;
  // iterate over s1
  while k < |s1|
    invariant 0 <= k <= |s1|
    invariant bal == CalcBal(s1, 0, k, 0)
    invariant forall i :: 0 <= i <= k ==> CalcBal(s1, 0, i, 0) >= 0
  {
    // update balance with next element
    if s1[k] == 0 {
      bal := bal + 1;
    } else {
      bal := bal - 1;
    }
    k := k + 1;
    CalcBal_step(s1, k-1);
    assert bal == CalcBal(s1, 0, k, 0);
    if bal < 0 {
      // witness for the existential in the postcondition
      assert 0 <= k <= |s1| && CalcBal(s1, 0, k, 0) < 0;
      return false;
    }
  }

  // Now iterate over s2, starting from total balance of s1
  var k2 := 0;
  // bal is already CalcBal(s1,0,|s1|,0)
  while k2 < |s2|
    invariant 0 <= k2 <= |s2|
    invariant bal == CalcBal(s1, 0, |s1|, 0) + CalcBal(s2, 0, k2, 0)
    invariant forall i :: 0 <= i <= k2 ==> CalcBal(s1, 0, |s1|, 0) + CalcBal(s2, 0, i, 0) >= 0
  {
    if s2[k2] == 0 {
      bal := bal + 1;
    } else {
      bal := bal - 1;
    }
    k2 := k2 + 1;
    CalcBal_step(s2, k2-1);
    assert bal == CalcBal(s1, 0, |s1|, 0) + CalcBal(s2, 0, k2, 0);
    if bal < 0 {
      // witness for the existential in the postcondition (second case)
      assert 0 <= k2 <= |s2| && CalcBal(s1, 0, |s1|, 0) + CalcBal(s2, 0, k2, 0) < 0;
      return false;
    }
  }

  // All prefixes satisfied
  return true;
}
// </vc-code>

