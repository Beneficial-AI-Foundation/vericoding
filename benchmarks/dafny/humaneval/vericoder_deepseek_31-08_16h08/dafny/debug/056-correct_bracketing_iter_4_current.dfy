function CalcBal(s: seq<int>, i: int, j: int) : int 
    requires 0 <= i <= j <= |s|
{
    if i == j then 0
    else (if s[j - 1] == 0 then 1 else -1) + CalcBal(s, i, j - 1)
}

// <vc-helpers>
lemma CalcBalNonNegative(s: seq<int>, i: int, j: int)
  requires 0 <= i <= j <= |s|
  requires forall k :: i <= k < j ==> CalcBal(s, i, k+1) >= 0
  ensures CalcBal(s, i, j) >= 0
{
  if i < j {
    var k := j - 1;
    CalcBalNonNegative(s, i, k);
    calc {
      CalcBal(s, i, j);
      == { CalcBalSplit(s, i, j, k); }
      CalcBal(s, i, k) + CalcBal(s, k, j);
      == { assert CalcBal(s, k, j) == (if s[j-1] == 0 then 1 else -1); }
      CalcBal(s, i, k) + (if s[j-1] == 0 then 1 else -1);
    }
    assert CalcBal(s, i, k) >= 0;
    assert forall l :: i <= l < j ==> CalcBal(s, i, l+1) >= 0;
    assert CalcBal(s, i, j-1) >= 0;
    assert CalcBal(s, i, j-1) == CalcBal(s, i, k);
  }
}

lemma CalcBalSplit(s: seq<int>, i: int, j: int, k: int)
  requires 0 <= i <= k <= j <= |s|
  ensures CalcBal(s, i, j) == CalcBal(s, i, k) + CalcBal(s, k, j)
{
  if j > i {
    if k == j {
      assert CalcBal(s, k, j) == 0;
    } else if k == i {
      // trivial case
    } else {
      CalcBalSplit(s, i, j-1, k);
      if k < j {
        assert CalcBal(s, i, j) == CalcBal(s, i, j-1) + (if s[j-1] == 0 then 1 else -1);
        assert CalcBal(s, k, j) == CalcBal(s, k, j-1) + (if s[j-1] == 0 then 1 else -1);
      }
    }
  }
}

lemma CalcBalStep(s: seq<int>, k: int)
  requires 0 <= k < |s|
  ensures CalcBal(s, 0, k+1) == CalcBal(s, 0, k) + (if s[k] == 0 then 1 else -1)
{
  // This is directly from the definition of CalcBal
}

lemma CalcBalMonotonic(s: seq<int>, i: int, j: int, k: int)
  requires 0 <= i <= j <= k <= |s|
  requires forall l :: i <= l < k ==> CalcBal(s, i, l+1) >= 0
  ensures CalcBal(s, i, j) >= 0
{
  if j < k {
    CalcBalNonNegative(s, i, j);
  } else if j == k {
    CalcBalNonNegative(s, i, j);
  }
}
// </vc-helpers>

// <vc-spec>
method correct_bracketing(s: seq<int>) returns (b: bool)
    // pre-conditions-start
    requires forall i :: 0 <= i < |s| ==> s[i] == 0 || s[i] == 1
    // pre-conditions-end
    // post-conditions-start
    ensures (forall i :: 0 <= i <= |s| ==> CalcBal(s, 0, i) >= 0) ==> b
    ensures b ==> (forall i :: 0 <= i <= |s| ==> CalcBal(s, 0, i) >= 0)
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var n := |s|;
  var balance := 0;
  b := true;
  
  var k := 0;
  while k < n
    invariant 0 <= k <= n
    invariant balance == CalcBal(s, 0, k)
    invariant balance >= 0
    invariant b == (forall i :: 0 <= i <= k ==> CalcBal(s, 0, i) >= 0)
  {
    CalcBalStep(s, k);
    var old_balance := balance;
    if s[k] == 0 {
      balance := balance + 1;
    } else {
      balance := balance - 1;
    }
    
    if balance < 0 {
      b := false;
    } else if b {
      // If we haven't found a negative balance yet, all prefixes up to k+1 are non-negative
      assert forall i :: 0 <= i <= k ==> CalcBal(s, 0, i) >= 0;
      assert CalcBal(s, 0, k+1) == balance >= 0;
    }
    k := k + 1;
  }
  
  if b {
    assert forall i :: 0 <= i <= n ==> CalcBal(s, 0, i) >= 0;
  } else {
    var m := 0;
    var temp_balance := 0;
    while m < n && temp_balance >= 0
      invariant 0 <= m <= n
      invariant temp_balance == CalcBal(s, 0, m)
      invariant forall i :: 0 <= i <= m ==> CalcBal(s, 0, i) >= 0
    {
      if s[m] == 0 {
        temp_balance := temp_balance + 1;
      } else {
        temp_balance := temp_balance - 1;
      }
      m := m + 1;
    }
    assert m < n ==> CalcBal(s, 0, m) < 0;
  }
}
// </vc-code>

