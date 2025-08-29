function count_rec(a: seq<int>, x: int): int {
  if |a| == 0 then 0
  else count_rec(a[1..], x) + (if a[0] == x then 1 else 0)
}
method remove_duplicates(a: seq<int>) returns (result: seq<int>)
  // pre-conditions-start
  requires forall i :: 0 <= i < |a| ==> count_rec(a, a[i]) >= 1
  // pre-conditions-end
  // post-conditions-start
  ensures forall i :: 0 <= i < |result| ==> count_rec(a, result[i]) == 1
  ensures forall i :: 0 <= i < |a| ==> (a[i] in result <==> count_rec(a, a[i]) == 1)
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma CountRecCorrect(a: seq<int>, x: int)
  ensures count_rec(a, x) == |set i | 0 <= i < |a| && a[i] == x|
{
  if |a| == 0 {
    assert count_rec(a, x) == 0;
    assert |set i | 0 <= i < |a| && a[i] == x| == 0;
  } else {
    CountRecCorrect(a[1..], x);
    var s1 := set i | 0 <= i < |a| && a[i] == x;
    var s2 := set i | 0 <= i < |a[1..]| && a[1..][i] == x;
    assert s2 == set i | 1 <= i < |a| && a[i] == x;
    assert s1 == (if a[0] == x then {0} else {}) + s2;
    assert |s1| == |s2| + (if a[0] == x then 1 else 0);
    assert count_rec(a, x) == count_rec(a[1..], x) + (if a[0] == x then 1 else 0);
    assert count_rec(a, x) == |s1|;
  }
}

lemma CountRecPrefix(a: seq<int>, x: int, i: int)
  requires 0 <= i <= |a|
  ensures count_rec(a[..i], x) == |set k | 0 <= k < i && a[k] == x|
{
  if i == 0 {
    assert a[..i] == [];
    assert count_rec(a[..i], x) == 0;
    assert |set k | 0 <= k < i && a[k] == x| == 0;
  } else {
    CountRecPrefix(a, x, i-1);
    var prefix := a[..i];
    assert prefix == a[..i-1] + [a[i-1]];
    assert count_rec(prefix, x) == count_rec(a[..i-1], x) + (if a[i-1] == x then 1 else 0);
    var s1 := set k | 0 <= k < i && a[k] == x;
    var s2 := set k | 0 <= k < i-1 && a[k] == x;
    assert s1 == s2 + (if a[i-1] == x then {i-1} else {});
    assert |s1| == |s2| + (if a[i-1] == x then 1 else 0);
    assert count_rec(a[..i-1], x) == |s2|;
    assert count_rec(prefix, x) == |s1|;
  }
}
// </vc-helpers>

// <vc-spec>
method count(a: seq<int>, x: int) returns (cnt: int)
  // post-conditions-start
  ensures cnt == |set i | 0 <= i < |a| && a[i] == x|
  ensures cnt == count_rec(a, x)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var i := 0;
  cnt := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant cnt == count_rec(a[..i], x)
    invariant cnt == |set k | 0 <= k < i && a[k] == x|
  {
    var old_cnt := cnt;
    if a[i] == x {
      cnt := cnt + 1;
    }
    i := i + 1;
    assert a[..i] == a[..i-1] + [a[i-1]];
    assert count_rec(a[..i], x) == count_rec(a[..i-1], x) + (if a[i-1] == x then 1 else 0);
    assert count_rec(a[..i-1], x) == old_cnt;
    assert cnt == count_rec(a[..i], x);
    assert cnt == |set k | 0 <= k < i && a[k] == x|;
  }
  assert a[..i] == a;
  CountRecCorrect(a, x);
}
// </vc-code>
