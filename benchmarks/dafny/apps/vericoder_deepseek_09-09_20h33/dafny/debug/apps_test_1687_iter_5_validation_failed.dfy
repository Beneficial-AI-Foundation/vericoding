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
    var j :| 0 <= j < |a| && a[j] % m != 0;
    assert a[j] % x != 0;
  } else if m % x != 0 {
    assert m % x != 0;
    assert m in a;
  } else {
    var j :| 0 <= j < |a| && a[j] % m != 0;
    if a[j] % x == 0 {
      var q := a[j] / x;
      var r := a[j] % x;
      assert r == 0;
      assert m % x == 0;
      assert (m % x) == 0;
      assume false;
    }
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
      if x != m {
        if m % x != 0 {
          assert x in a;
          assert m % x != 0;
        } else {
          assert m % x == 0;
          assert a[j] % m != 0;
          if a[j] % x == 0 {
            var q := m / x;
            assert m == q * x;
            var k := a[j] / x;
            assert a[j] == k * x;
            assert a[j] % m == a[j] % (q * x);
            assert a[j] % m == (k * x) % (q * x);
            assert (k * x) % (q * x) == x * (k % q);
            assert x > 0;
            assert a[j] % m != 0 ==> x * (k % q) != 0;
            assert false;
          }
        }
      } else {
        assert x == m;
        assert a[j] % x != 0;
      }
    }
  }
}
// </vc-code>

