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

lemma lemma_exists_non_divisor(a: seq<int>, d: int)
  requires |a| > 0 && d > 0
  requires exists i :: 0 <= i < |a| && a[i] % d != 0
  ensures forall x :: x in a ==> exists i :: 0 <= i < |a| && a[i] % x != 0
{
}

lemma lemma_min_property(a: seq<int>)
  requires |a| > 0
  ensures forall i :: 0 <= i < |a| ==> min(a) <= a[i]
{
}

lemma lemma_min_divisibility(a: seq<int>)
  requires |a| > 0
  ensures (forall i :: 0 <= i < |a| ==> a[i] % min(a) == 0) || 
          (exists i :: 0 <= i < |a| && a[i] % min(a) != 0)
{
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
  if forall i | 0 <= i < |a| :: a[i] % m == 0 {
    result := m;
  } else {
    result := -1;
  }
}
// </vc-code>

