

// <vc-helpers>
// No helpers required
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
  ghost var s := [] : seq<int>;
  while i < n
    invariant 0 <= i <= n
    invariant result == sum(s)
    invariant |s| == i
    invariant forall k :: 0 <= k < |s| ==> s[k] == (if k % 11 == 0 || k % 13 == 0 then count7_r(k) else 0)
  {
    var val := if i % 11 == 0 || i % 13 == 0 then count7_r(i) else 0;
    s := s + [val];
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