function count_rec(a: seq<int>, x: int): int {
  if |a| == 0 then 0
  else count_rec(a[1..], x) + (if a[0] == x then 1 else 0)
}

// <vc-helpers>
lemma count_rec_membership(a: seq<int>, x: int)
  ensures count_rec(a, x) > 0 <==> x in a
{
  if |a| == 0 {
    assert count_rec(a, x) == 0;
    assert x !in a;
  } else {
    count_rec_membership(a[1..], x);
    if a[0] == x {
      assert count_rec(a, x) == count_rec(a[1..], x) + 1;
      assert count_rec(a, x) > 0;
      assert x in a;
    } else {
      assert count_rec(a, x) == count_rec(a[1..], x);
      assert x in a <==> x in a[1..];
      assert count_rec(a, x) > 0 <==> count_rec(a[1..], x) > 0;
      assert count_rec(a[1..], x) > 0 <==> x in a[1..];
      assert count_rec(a, x) > 0 <==> x in a;
    }
  }
}

lemma count_rec_positive(a: seq<int>, x: int)
  requires x in a
  ensures count_rec(a, x) >= 1
{
  count_rec_membership(a, x);
  assert count_rec(a, x) > 0;
}

lemma count_rec_unique_means_one(a: seq<int>, x: int)
  requires x in a
  requires forall i, j :: 0 <= i < j < |a| && a[i] == x && a[j] == x ==> false
  ensures count_rec(a, x) == 1
{
  if |a| == 0 {
    assert x !in a;
    assert false;
  } else {
    if a[0] == x {
      assert forall i :: 1 <= i < |a| ==> a[i] != x;
      assert forall y :: y in a[1..] ==> y != x;
      assert x !in a[1..];
      count_rec_membership(a[1..], x);
      assert count_rec(a[1..], x) == 0;
      assert count_rec(a, x) == count_rec(a[1..], x) + 1 == 1;
    } else {
      assert x in a[1..];
      assert forall i, j :: 0 <= i < j < |a[1..]| && a[1..][i] == x && a[1..][j] == x ==> false;
      count_rec_unique_means_one(a[1..], x);
      assert count_rec(a[1..], x) == 1;
      assert count_rec(a, x) == count_rec(a[1..], x) + 0 == 1;
    }
  }
}

lemma count_rec_determines_membership_uniqueness(a: seq<int>, x: int)
  ensures count_rec(a, x) == 1 ==> (x in a && forall i, j :: 0 <= i < j < |a| && a[i] == x && a[j] == x ==> false)
{
  if count_rec(a, x) == 1 {
    count_rec_membership(a, x);
    assert x in a;
    
    if exists i, j :: 0 <= i < j < |a| && a[i] == x && a[j] == x {
      var i, j :| 0 <= i < j < |a| && a[i] == x && a[j] == x;
      assert count_rec(a, x) >= 2;
      assert false;
    }
  }
}

lemma count_rec_at_index(a: seq<int>, i: int)
  requires 0 <= i < |a|
  ensures count_rec(a, a[i]) >= 1
{
  count_rec_membership(a, a[i]);
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method remove_duplicates(a: seq<int>) returns (result: seq<int>)
Process input. Requires: the condition holds for all values. Ensures: the condition holds for all values; the condition holds for all values.
*/
// </vc-description>

// <vc-spec>
method remove_duplicates(a: seq<int>) returns (result: seq<int>)
  // pre-conditions-start
  requires forall i :: 0 <= i < |a| ==> count_rec(a, a[i]) >= 1
  // pre-conditions-end
  // post-conditions-start
  ensures forall i :: 0 <= i < |result| ==> count_rec(a, result[i]) == 1
  ensures forall i :: 0 <= i < |a| ==> (a[i] in result <==> count_rec(a, a[i]) == 1)
  // post-conditions-end
// </vc-spec>

// <vc-code>
{
  result := [];
  var i := 0;
  
  while i < |a|
    invariant 0 <= i <= |a|
    invariant forall j :: 0 <= j < |result| ==> count_rec(a, result[j]) == 1
    invariant forall j :: 0 <= j < i ==> (a[j] in result <==> count_rec(a, a[j]) == 1)
    invariant forall j :: 0 <= j < |result| ==> result[j] in a
  {
    count_rec_at_index(a, i);
    if a[i] !in result {
      if count_rec(a, a[i]) == 1 {
        count_rec_determines_membership_uniqueness(a, a[i]);
        result := result + [a[i]];
      }
    }
    i := i + 1;
  }
}
// </vc-code>

method count(a: seq<int>, x: int) returns (cnt: int)
  // post-conditions-start
  ensures cnt == |set i | 0 <= i < |a| && a[i] == x|
  ensures cnt == count_rec(a, x)
  // post-conditions-end
{
  assume{:axiom} false;
}