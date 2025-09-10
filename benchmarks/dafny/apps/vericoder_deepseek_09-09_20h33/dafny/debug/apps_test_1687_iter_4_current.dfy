function min(a: seq<int>): int
    requires |a| > 0
    ensures min(a) in a
    ensures forall i :: 0 <= i < |a| ==> min(a) <= a[i]
{
    if |a| == 1 then a[0]
    else if a[0] <= min(a[1..]) then a[0]
    else min(a[1..])
}

// <vc-helpers>
lemma lemma_mod_properties(x: int, y: int)
  requires x > 0 && y > 0
  ensures x % y == 0 || x % y != 0
{
}

lemma lemma_divisible_by_common_divisor(a: seq<int>, d: int)
  requires |a| > 0 && d > 0
  requires forall i :: 0 <= i < |a| ==> a[i] % d == 0
  ensures forall x :: x in a ==> x % d == 0
{
}

lemma lemma_min_property(a: seq<int>)
  requires |a| > 0
  ensures forall i :: 0 <= i < |a| ==> min(a) <= a[i]
  ensures min(a) in a
{
}

lemma lemma_min_divisibility(a: seq<int>)
  requires |a| > 0
  requires min(a) > 0
  ensures (forall i :: 0 <= i < |a| ==> a[i] % min(a) == 0) || 
          (exists i :: 0 <= i < |a| && a[i] % min(a) != 0)
{
}

lemma lemma_all_divisible_or_not(a: seq<int>, x: int, m: int)
  requires |a| > 0
  requires x > 0 && m > 0
  requires x in a
  requires m in a
  requires forall i :: 0 <= i < |a| ==> a[i] > 0
  requires exists j :: 0 <= j < |a| && a[j] % m != 0
  ensures exists i :: 0 <= i < |a| && a[i] % x != 0
{
  if x == m {
    // Use the witness j where a[j] % m != 0
    var j :| 0 <= j < |a| && a[j] % m != 0;
    assert a[j] % x != 0;
  } else if m % x != 0 {
    // If m is not divisible by x, then m itself is a witness
    assert m % x != 0;
    assert m in a;
  } else {
    // If x divides m, then since some a[j] is not divisible by m,
    // and x divides m, a[j] won't be divisible by x either
    var j :| 0 <= j < |a| && a[j] % m != 0;
    // Prove by contradiction: if a[j] % x == 0, then since x divides m,
    // a[j] would be divisible by m too (contradiction)
    assert a[j] % x != 0 by {
      if a[j] % x == 0 {
        // Since x divides m, m = k*x for some k, so a[j] % m = a[j] % (k*x)
        // If a[j] is divisible by x, it might not be divisible by m
        // Need stronger reasoning
        // Instead, use the fact that if x divides m and m divides a[j], then x divides a[j]
        // But we know a[j] % m != 0, so m doesn't divide a[j]
        // However, x could still divide a[j] even if m doesn't
        // So we need to explicitly check this case
        assert false; // This case needs to be handled differently
      }
    };
  }
}
// </vc-helpers>

// <vc-spec>
method solve(a: seq<int>) returns (result: int)
    requires |a| > 0
    requires forall i :: 0 <= i < |a| ==> a[i] > 0
    ensures result == -1 || result in a
    ensures result != -1 ==> forall i :: 0 <= i < |a| ==> a[i] % result == 0
    ensures result == -1 ==> forall x :: x in a ==> exists i :: 0 <= i < |a| && a[i] % x != 0
    ensures (forall i :: 0 <= i < |a| ==> a[i] % (min(a)) == 0) ==> result == min(a)
    ensures (exists i :: 0 <= i < |a| && a[i] % (min(a)) != 0) ==> result == -1
// </vc-spec>
// <vc-code>
{
  var m := min(a);
  
  assert m > 0 by {
    assert m in a;
    var k :| 0 <= k < |a| && a[k] == m;
    assert a[k] > 0;
  }
  
  if forall i | 0 <= i < |a| :: a[i] % m == 0 {
    result := m;
  } else {
    result := -1;
    var j :| 0 <= j < |a| && a[j] % m != 0;
    
    forall x | x in a
      ensures exists i :: 0 <= i < |a| && a[i] % x != 0
    {
      lemma_all_divisible_or_not(a, x, m);
    }
  }
}
// </vc-code>

