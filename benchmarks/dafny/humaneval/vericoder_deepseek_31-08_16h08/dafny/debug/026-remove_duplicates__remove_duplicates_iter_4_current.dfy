function count_rec(a: seq<int>, x: int): int {
  if |a| == 0 then 0
  else count_rec(a[1..], x) + (if a[0] == x then 1 else 0)
}

// <vc-helpers>
lemma count_rec_append(a: seq<int>, b: seq<int>, x: int)
  ensures count_rec(a + b, x) == count_rec(a, x) + count_rec(b, x)
  decreases |a|
{
  if |a| == 0 {
  } else {
    count_rec_append(a[1..], b, x);
  }
}

lemma count_rec_contains(a: seq<int>, x: int)
  ensures (x in a) <==> count_rec(a, x) > 0
  decreases |a|
{
  if |a| == 0 {
  } else {
    if a[0] == x {
    } else {
      count_rec_contains(a[1..], x);
    }
  }
}

lemma count_rec_remove(a: seq<int>, i: int, x: int)
  requires 0 <= i < |a|
  ensures count_rec(a, x) == count_rec(a[i..i+1], x) + count_rec(a[..i] + a[i+1..], x)
{
  count_rec_append(a[..i], a[i..i+1], x);
  count_rec_append(a[..i] + a[i..i+1], a[i+1..], x);
  assert a == (a[..i] + a[i..i+1]) + a[i+1..];
}

lemma count_rec_remove_single(a: seq<int>, x: int)
  requires |a| == 1
  ensures count_rec(a, x) == (if a[0] == x then 1 else 0)
{
}

ghost function filter_out_b(s: seq<int>, b: seq<int>): seq<int>
  decreases |s|
{
  if |s| == 0 then []
  else (if s[0] in b then [] else [s[0]]) + filter_out_b(s[1..], b)
}

lemma count_rec_preserved(a: seq<int>, b: seq<int>, x: int)
  requires forall i :: 0 <= i < |a| ==> (a[i] in b <==> count_rec(b, a[i]) == 1)
  ensures count_rec(a, x) == count_rec(b, x) + count_rec(filter_out_b(a, b), x)
  decreases |a|
{
  if |a| == 0 {
  } else {
    var head := a[0];
    var tail := a[1..];
    if head in b {
      assert head in b;
      assert count_rec(b, head) == 1;
      count_rec_preserved(tail, b, x);
    } else {
      count_rec_preserved(tail, b, x);
    }
  }
}

lemma count_rec_single(x: int, y: int)
  ensures count_rec([x], y) == (if x == y then 1 else 0)
{
}

lemma count_rec_result_invariant(a: seq<int>, result: seq<int>, x: int)
  requires forall z :: z in result ==> count_rec(a, z) == 1
  requires forall z :: z in result ==> count_rec(result, z) == 1
  ensures x in result ==> count_rec(result, x) == 1
{
}

lemma count_rec_not_in_result(a: seq<int>, result: seq<int>, x: int)
  requires x !in result
  ensures count_rec(result + [x], x) == 1
{
  count_rec_single(x, x);
  count_rec_append(result, [x], x);
}
// </vc-helpers>
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
    invariant forall x :: x in result ==> count_rec(a, x) == 1
    invariant forall j :: 0 <= j < i ==> (a[j] in result <==> count_rec(a, a[j]) == 1)
    invariant forall x :: x in result ==> x in a
    invariant forall x :: x in result ==> count_rec(result, x) == 1
  {
    if count_rec(a, a[i]) == 1 {
      if a[i] !in result {
        result := result + [a[i]];
        assert count_rec(result, a[i]) == 1;
        assert forall x :: x in result ==> count_rec(result, x) == 1;
      } else {
        assert count_rec(result, a[i]) == 1;
      }
    } else {
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