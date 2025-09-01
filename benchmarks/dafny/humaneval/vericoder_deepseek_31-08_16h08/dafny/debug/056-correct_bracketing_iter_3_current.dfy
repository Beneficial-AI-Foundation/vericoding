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
    calc {
      CalcBal(s, i, j);
      == { CalcBalSplit(s, i, j, j-1); }
      CalcBal(s, i, j-1) + CalcBal(s, j-1, j);
      == { assert CalcBal(s, j-1, j) == (if s[j-1] == 0 then 1 else -1); }
      CalcBal(s, i, j-1) + (if s[j-1] == 0 then 1 else -1);
    }
    CalcBalNonNegative(s, i, j-1);
  }
}

lemma CalcBalSplit(s: seq<int>, i: int, j: int, k: int)
  requires 0 <= i <= k <= j <= |s|
  ensures CalcBal(s, i, j) == CalcBal(s, i, k) + CalcBal(s, k, j)
{
  if k == j {
    assert CalcBal(s, k, j) == 0;
  } else if i == j {
    // trivial case
  } else {
    CalcBalSplit(s, i, j-1, k);
    if k < j {
      assert CalcBal(s, i, j) == CalcBal(s, i, j-1) + (if s[j-1] == 0 then 1 else -1);
      assert CalcBal(s, k, j) == CalcBal(s, k, j-1) + (if s[j-1] == 0 then 1 else -1);
    }
  }
}

lemma CalcBalStep(s: seq<int>, k: int)
  requires 0 <= k < |s|
  ensures CalcBal(s, 0, k+1) == CalcBal(s, 0, k) + (if s[k] == 0 then 1 else -1)
{
  calc {
    CalcBal(s, 0, k+1);
    == // by definition
    (if s[k] == 0 then 1 else -1) + CalcBal(s, 0, k);
    == // commutative
    CalcBal(s, 0, k) + (if s[k] == 0 then 1 else -1);
  }
}

lemma CalcBalMonotonic(s: seq<int>, i: int, j: int, k: int)
  requires 0 <= i <= j <= k <= |s|
  requires forall l :: i <= l < k ==> CalcBal(s, i, l+1) >= 0
  ensures CalcBal(s, i, j) >= 0
{
  if j < k {
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
    } else {
      // Maintain the invariant that all prefixes up to k+1 are non-negative
      assert forall i :: 0 <= i <= k+1 ==> CalcBal(s, 0, i) >= 0;
    }
    k := k + 1;
  }
  
  if b {
    assert forall i :: 0 <= i <= n ==> CalcBal(s, 0, i) >= 0;
  } else {
    // Find the first position where balance becomes negative
    var m := 0;
    while m < n && CalcBal(s, 0, m+1) >= 0
      invariant 0 <= m <= n
      invariant forall i :: 0 <= i <= m ==> CalcBal(s, 0, i) >= 0
    {
      m := m + 1;
    }
    if m < n {
      assert CalcBal(s, 0, m+1) < 0;
    }
  }
}
// </vc-code>

