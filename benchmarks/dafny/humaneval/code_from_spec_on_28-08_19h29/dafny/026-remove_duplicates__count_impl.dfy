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
function countRec(a: seq<int>, x: int): int
  decreases |a|
{
  if |a| == 0 then 0
  else countRec(a[1..], x) + (if a[0] == x then 1 else 0)
}

lemma CountRecPrefix(a: seq<int>, x: int, i: int)
  requires 0 <= i <= |a|
  ensures countRec(a[..i], x) + countRec(a[i..], x) == countRec(a, x)
  decreases |a|
{
  if i == 0 {
    assert a[..0] == [];
    assert countRec(a[..0], x) == 0;
    assert countRec(a, x) == countRec(a[i..], x);
  } else if i == |a| {
    assert a[..i] == a;
    assert a[i..] == [];
    assert countRec(a[i..], x) == 0;
    assert countRec(a[..i], x) == countRec(a, x);
  } else {
    var prefix := a[..i];
    var suffix := a[i..];
    assert a == prefix + suffix;
    CountRecPrefix(a[1..], x, i-1);
    assert countRec(a, x) == (if a[0] == x then 1 else 0) + countRec(a[1..], x);
    assert countRec(prefix + suffix, x) == countRec(prefix, x) + countRec(suffix, x);
  }
}

lemma CountRecAppend(a: seq<int>, x: int, i: int)
  requires 0 <= i < |a|
  ensures countRec(a[..i+1], x) == countRec(a[..i], x) + (if a[i] == x then 1 else 0)
{
  var prefix := a[..i];
  var single := [a[i]];
  assert a[..i+1] == prefix + single;
  assert countRec(a[..i+1], x) == countRec(prefix, x) + countRec(single, x);
  assert countRec(single, x) == (if a[i] == x then 1 else 0);
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method count(a: seq<int>, x: int) returns (cnt: int)
Count occurrences. Ensures: returns the correct count; returns the correct count.
*/
// </vc-description>

// <vc-spec>
method count(a: seq<int>, x: int) returns (cnt: int)
  ensures cnt == countRec(a, x)
// </vc-spec>
// <vc-code>
{
  cnt := 0;
  var i := 0;
  while i < |a|
    invariant 0 <= i <= |a|
    invariant cnt == countRec(a[..i], x)
  {
    if a[i] == x {
      cnt := cnt + 1;
    }
    i := i + 1;
    assert cnt == countRec(a[..i], x) by {
      if i > 0 {
        CountRecAppend(a, x, i-1);
      }
    }
  }
}
// </vc-code>
