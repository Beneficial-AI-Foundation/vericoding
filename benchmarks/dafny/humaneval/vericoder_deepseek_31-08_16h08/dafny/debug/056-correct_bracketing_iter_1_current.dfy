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
    CalcBalNonNegative(s, i, j-1);
  }
}

lemma CalcBalSplit(s: seq<int>, i: int, j: int, k: int)
  requires 0 <= i <= k <= j <= |s|
  ensures CalcBal(s, i, j) == CalcBal(s, i, k) + CalcBal(s, k, j)
{
  if i < j {
    if k < j {
      CalcBalSplit(s, i, j-1, k);
    }
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
    if s[k] == 0 {
      balance := balance + 1;
    } else {
      balance := balance - 1;
    }
    
    if balance < 0 {
      b := false;
    }
    k := k + 1;
    
    // Helper lemma application
    if k < n {
      CalcBalNonNegative(s, 0, k);
    }
  }
  
  if b {
    // Final verification that the entire sequence is balanced
    assert balance == CalcBal(s, 0, n);
    assert CalcBal(s, 0, n) >= 0;
    calc {
      forall i :: 0 <= i <= n ==> CalcBal(s, 0, i) >= 0;
    => {
      assert forall i :: 0 <= i <= n ==> CalcBal(s, 0, i) >= 0;
    }
    }
  } else {
    // Find the position where it becomes negative
    var m := 0;
    while m <= n && CalcBal(s, 0, m) >= 0
      invariant 0 <= m <= n
      invariant forall i :: 0 <= i <= m ==> CalcBal(s, 0, i) >= 0
    {
      m := m + 1;
    }
    assert m <= n && CalcBal(s, 0, m) < 0;
  }
}
// </vc-code>

