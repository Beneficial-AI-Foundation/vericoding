method remove_duplicates(a: seq<int>) returns (result: seq<int>)
  // pre-conditions-start
  requires forall i :: 0 <= i < |a| ==> count_rec(a, a[i]) >= 1
  // pre-conditions-end
  // post-conditions-start
  ensures forall i :: 0 <= i < |result| ==> count_rec(a, result[i]) == 1
  ensures forall i :: 0 <= i < |a| ==> (a[i] in result <==> count_rec(a, a[i]) == 1)
  // post-conditions-end
{
  // impl-start
  var res: seq<int> := [];
  for i := 0 to |a|
    // invariants-start
    invariant forall j :: 0 <= j < |res| ==> count_rec(a, res[j]) == 1
    invariant forall j :: 0 <= j < i ==> (a[j] in res <==> count_rec(a, a[j]) == 1)
    invariant forall j :: 0 <= j < |res| ==> res[j] in a[..i]
    // invariants-end
  {
    var cnt := count(a, a[i]);
    if cnt == 1 {
      res := res + [a[i]];
    }
  }
  result := res;
  // impl-end
}

function count_rec(a: seq<int>, x: int): int {
  if |a| == 0 then 0
  else count_rec(a[1..], x) + (if a[0] == x then 1 else 0)
}
// pure-end
lemma count_prop(s: seq<int>, x: int)
    requires |s| > 0
    ensures count_rec(s, x) == count_rec(s[..|s| - 1], x) + if s[|s| - 1] == x then 1 else 0
{
    if (|s| > 1) {
        assert (s[1..][..|s[1..]| - 1]) == s[1..|s| - 1];
    }
}
// pure-end
method count(a: seq<int>, x: int) returns (cnt: int)
  // post-conditions-start
  ensures cnt == |set i | 0 <= i < |a| && a[i] == x|
  ensures cnt == count_rec(a, x)
  // post-conditions-end
{
  // impl-start
  cnt := 0;
  ghost var positions: set<int> := {};
  for i := 0 to |a|
    // invariants-start
    invariant cnt == |positions|
    invariant positions == set k | 0 <= k < i && a[k] == x
    invariant cnt == count_rec(a[..i], x)
    // invariants-end
  {
    if a[i] == x {
      cnt := cnt + 1;
      positions := positions + {i};
    }
    // assert-start
    assert count_rec(a[..i + 1], x) == count_rec(a[..i], x) + (if a[i] == x then 1 else 0) by {
        assert a[..i+1][..i] == a[..i];
        count_prop(a[..i + 1], x);
    }
    // assert-end
  }
  assert a == a[..|a|]; // assert-line
  // impl-end
}
