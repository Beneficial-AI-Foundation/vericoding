

// <vc-helpers>
lemma SumAppendLast(s: seq<int>, x: int)
  ensures sum(s + [x]) == sum(s) + x
{
  if |s| == 0 {
    assert s == [];
    assert sum(s + [x]) == sum([x]);
    assert sum([x]) == x;
    assert sum(s) == 0;
    assert sum(s + [x]) == sum(s) + x;
  } else {
    var tl := s[1..];
    assert |s| > 0;
    assert |s + [x]| == |s| + 1;
    assert (s + [x])[0] == s[0];
    assert (s + [x])[1..] == tl + [x];
    assert sum(s) == s[0] + sum(tl);
    assert sum(s + [x]) == (s + [x])[0] + sum((s + [x])[1..]);
    assert sum(s + [x]) == s[0] + sum(tl + [x]);
    SumAppendLast(tl, x);
    assert sum(tl + [x]) == sum(tl) + x;
    assert s[0] + sum(tl + [x]) == s[0] + sum(tl) + x;
    assert sum(s + [x]) == sum(s) + x;
  }
}
// </vc-helpers>

// <vc-spec>
method fizz_buzz(n: nat) returns (result: nat)
  // post-conditions-start
  ensures result == sum(
    seq(n, i requires 0 <= i < n => (if i % 11 == 0 || i % 13 == 0 then count7_r(i) else 0))
  )
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  result := 0;
  var i := 0;
  ghost var s: seq<int> := [];
  while i < n
    invariant 0 <= i <= n
    invariant result == sum(s)
    invariant |s| == i
    invariant forall k :: 0 <= k < |s| ==> s[k] == (if k % 11 == 0 || k % 13 == 0 then count7_r(k) else 0)
  {
    var val := if i % 11 == 0 || i % 13 == 0 then count7_r(i) else 0;
    ghost var olds := s;
    s := olds + [val];
    SumAppendLast(olds, val);
    result := result + val;
    i := i + 1;
  }
  assert s == seq(n, j requires 0 <= j < n => (if j % 11 == 0 || j % 13 == 0 then count7_r(j) else 0));
  assert result == sum(s);
}
// </vc-code>

method count7(x: nat) returns (count: nat) 
  // post-conditions-start
  ensures count == count7_r(x)
  // post-conditions-end
{
  assume{:axiom} false;
}
function count7_r(x: nat): nat {
  var lst := if x % 10 == 7 then 1 else 0;
  if x < 10 then lst else lst + count7_r(x / 10)
}
// pure-end
function sum(s: seq<int>) : int {
  if |s| == 0 then 0 else s[0] + sum(s[1..])
}
// pure-end