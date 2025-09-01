function count_rec(a: seq<int>, x: int): int {
  if |a| == 0 then 0
  else count_rec(a[1..], x) + (if a[0] == x then 1 else 0)
}

// <vc-helpers>
lemma count_rec_non_negative(a: seq<int>, x: int)
  ensures count_rec(a, x) >= 0
{
  if |a| == 0 {
  } else {
    count_rec_non_negative(a[1..], x);
  }
}

lemma count_rec_zero_iff_not_in(a: seq<int>, x: int)
  ensures count_rec(a, x) == 0 <==> x !in a
{
  if |a| == 0 {
  } else {
    count_rec_zero_iff_not_in(a[1..], x);
  }
}

lemma count_rec_positive_iff_in(a: seq<int>, x: int)
  ensures count_rec(a, x) > 0 <==> x in a
{
  count_rec_zero_iff_not_in(a, x);
  count_rec_non_negative(a, x);
}

lemma count_rec_append(a: seq<int>, b: seq<int>, x: int)
  ensures count_rec(a + b, x) == count_rec(a, x) + count_rec(b, x)
{
  if |a| == 0 {
    assert a + b == b;
  } else {
    assert a + b == [a[0]] + (a[1..] + b);
    count_rec_append(a[1..], b, x);
  }
}

lemma count_rec_single(x: int, y: int)
  ensures count_rec([x], y) == (if x == y then 1 else 0)
{
}

lemma count_rec_prefix(a: seq<int>, x: int, i: int)
  requires 0 <= i <= |a|
  ensures count_rec(a[..i], x) <= count_rec(a, x)
{
  if i == 0 {
    assert a[..i] == [];
  } else if i == |a| {
    assert a[..i] == a;
  } else {
    assert a == a[..i] + a[i..];
    count_rec_append(a[..i], a[i..], x);
    count_rec_non_negative(a[i..], x);
  }
}
// </vc-helpers>

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
  {
    var cnt := count(a, a[i]);
    if cnt == 1 {
      result := result + [a[i]];
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