method fizz_buzz(n: nat) returns (result: nat)
  // post-conditions-start
  ensures result == sum(
    seq(n, i requires 0 <= i < n => (if i % 11 == 0 || i % 13 == 0 then count7_r(i) else 0))
  )
  // post-conditions-end
{
  // impl-start
  ghost var values := [];
  result := 0;
  var i := 0;
  while i < n
    // invariants-start
    invariant 0 <= i <= n
    invariant |values| == i
    invariant result == sum(values[..i])
    invariant values == seq(i, j requires 0 <= j < i => (if j % 11 == 0 || j % 13 == 0 then count7_r(j) else 0))
    // invariants-end
  {
    ghost var pre := values;
    if i % 11 == 0 || i % 13 == 0 {
      var cnt := count7(i);
      result := result + cnt;
      values := values + [cnt];
    } else {
      values := values + [0];
    }
    assert values[..i] == pre[..i]; // assert-line
    // assert-start
    assert sum(values[..i + 1]) == sum(values[..i]) + values[i] by {
      assert values[..i+1][..i] == values[..i];
      sum_prop(values[..i + 1]);
    }
    // assert-end
    i := i + 1;
  }
  assert values[..|values|] == values; // assert-line
  // impl-end
}

method count7(x: nat) returns (count: nat) 
  // post-conditions-start
  ensures count == count7_r(x)
  // post-conditions-end
{
  // impl-start
  count := 0;
  var y := x;
  while y > 0
    // invariants-start
    invariant count + count7_r(y) == count7_r(x)
    // invariants-end
  {
    if y % 10 == 7 {
      count := count + 1;
    }
    y := y / 10;
  } 
  // impl-end
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
lemma sum_prop(s: seq<int>)
  requires |s| > 0
  ensures sum(s) == sum(s[..|s| - 1]) + s[ |s| - 1 ]
{
  if (|s| > 1) {
    assert (s[1..][..|s[1..]| - 1]) == s[1..|s| - 1];
  }
}
// pure-end
