// <vc-preamble>
function count7_r(x: nat): nat {
  var lst := if x % 10 == 7 then 1 else 0;
  if x < 10 then lst else lst + count7_r(x / 10)
}

function sum(s: seq<int>) : int {
  if |s| == 0 then 0 else s[0] + sum(s[1..])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): lemma sum(s + [x]) = sum(s) + x */
lemma sum_concat_single(s: seq<int>, x: int)
  ensures sum(s + [x]) == sum(s) + x
  decreases |s|
{
  if |s| == 0 {
    assert sum([] + [x]) == sum([]) + x;
  } else {
    var s0 := s[0];
    var rest := s[1..];
    assert s == [s0] + rest;
    assert s + [x] == [s0] + (rest + [x]);
    assert sum(s + [x]) == s0 + sum(rest + [x]);
    sum_concat_single(rest, x);
    assert sum(rest + [x]) == sum(rest) + x;
    assert s0 + sum(rest + [x]) == s0 + sum(rest) + x;
    assert sum(s) == s0 + sum(rest);
    assert s0 + sum(rest) + x == sum(s) + x;
  }
}

/* helper modified by LLM (iteration 3): lemma to show constructed seq equals comprehension */
lemma seq_builds_equal(n: nat, s: seq<int>)
  requires |s| == n
  requires forall j :: 0 <= j < n ==> s[j] == (if j % 11 == 0 || j % 13 == 0 then count7_r(j) else 0)
  ensures s == seq(n, j requires 0 <= j < n => (if j % 11 == 0 || j % 13 == 0 then count7_r(j) else 0))
  decreases n
{
  if n == 0 {
  } else {
    assert s == s[..n-1] + [s[n-1]];
    seq_builds_equal(n-1, s[..n-1]);
    assert s[n-1] == (if (n-1) % 11 == 0 || (n-1) % 13 == 0 then count7_r(n-1) else 0);
    assert s[..n-1] + [s[n-1]] == seq(n-1, j requires 0 <= j < n-1 => (if j % 11 == 0 || j % 13 == 0 then count7_r(j) else 0)) + [(if (n-1) % 11 == 0 || (n-1) % 13 == 0 then count7_r(n-1) else 0)];
    assert seq(n-1, j requires 0 <= j < n-1 => (if j % 11 == 0 || j % 13 == 0 then count7_r(j) else 0)) + [(if (n-1) % 11 == 0 || (n-1) % 13 == 0 then count7_r(n-1) else 0)] == seq(n, j requires 0 <= j < n => (if j % 11 == 0 || j % 13 == 0 then count7_r(j) else 0));
  }
}
// </vc-helpers>

// <vc-spec>
method fizz_buzz(n: nat) returns (result: nat)

  ensures result == sum(
    seq(n, i requires 0 <= i < n => (if i % 11 == 0 || i % 13 == 0 then count7_r(i) else 0))
  )
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): build sequence and accumulate sum */
{
  var seq_s: seq<int> := [];
  var acc: nat := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant |seq_s| == i
    invariant acc == sum(seq_s)
    invariant forall j :: 0 <= j < i ==> seq_s[j] == (if j % 11 == 0 || j % 13 == 0 then count7_r(j) else 0)
  {
    var v := if i % 11 == 0 || i % 13 == 0 then count7_r(i) else 0;
    var seq_old := seq_s;
    var acc_old := acc;
    seq_s := seq_old + [v];
    sum_concat_single(seq_old, v);
    acc := acc_old + v;
    assert acc == sum(seq_s);
    i := i + 1;
  }
  seq_builds_equal(n, seq_s);
  assert acc == sum(seq_s);
  result := acc;
  assert result == sum(seq(n, j requires 0 <= j < n => (if j % 11 == 0 || j % 13 == 0 then count7_r(j) else 0)));
}

// </vc-code>
