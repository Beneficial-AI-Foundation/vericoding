// <vc-helpers>
function count7_seq(n: nat, i: nat): seq<int>
  requires 0 <= i <= n
  decreases n - i
{
  if i == n then []
  else [(if i % 11 == 0 || i % 13 == 0 then count7_r(i) else 0)] + count7_seq(n, i + 1)
}

lemma SumCount7Lemma(n: nat, i: nat)
  requires 0 <= i <= n
  ensures sum(count7_seq(n, i)) == sum(seq(n - i, j requires 0 <= j < n - i => (if (i + j) % 11 == 0 || (i + j) % 13 == 0 then count7_r(i + j) else 0)))
  decreases n - i
{
  if i == n {
    assert count7_seq(n, i) == [];
    assert seq(n - i, j requires 0 <= j < n - i => (if (i + j) % 11 == 0 || (i + j) % 13 == 0 then count7_r(i + j) else 0)) == [];
    assert sum([]) == 0;
  } else {
    var curr_seq := count7_seq(n, i);
    var rest_seq := count7_seq(n, i + 1);
    assert curr_seq == [(if i % 11 == 0 || i % 13 == 0 then count7_r(i) else 0)] + rest_seq;
    calc {
      sum(curr_seq);
      sum([(if i % 11 == 0 || i % 13 == 0 then count7_r(i) else 0)] + rest_seq);
      (if i % 11 == 0 || i % 13 == 0 then count7_r(i) else 0) + sum(rest_seq);
      {
        SumCount7Lemma(n, i + 1);
        assert sum(rest_seq) == sum(seq(n - (i + 1), j requires 0 <= j < n - (i + 1) => (if (i + 1 + j) % 11 == 0 || (i + 1 + j) % 13 == 0 then count7_r(i + 1 + j) else 0)));
      }
      (if i % 11 == 0 || i % 13 == 0 then count7_r(i) else 0) + sum(seq(n - (i + 1), j requires 0 <= j < n - (i + 1) => (if (i + 1 + j) % 11 == 0 || (i + 1 + j) % 13 == 0 then count7_r(i + 1 + j) else 0)));
    }
    var full_seq := seq(n - i, j requires 0 <= j < n - i => (if (i + j) % 11 == 0 || (i + j) % 13 == 0 then count7_r(i + j) else 0));
    assert full_seq[0] == (if i % 11 == 0 || i % 13 == 0 then count7_r(i) else 0);
    assert full_seq[1..] == seq(n - (i + 1), j requires 0 <= j < n - (i + 1) => (if (i + 1 + j) % 11 == 0 || (i + 1 + j) % 13 == 0 then count7_r(i + 1 + j) else 0));
    assert sum(full_seq) == full_seq[0] + sum(full_seq[1..]);
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
method FizzBuzz(n: nat) returns (result: nat)
  ensures result == sum(seq(n, i requires 0 <= i < n => (if i % 11 == 0 || i % 13 == 0 then count7_r(i) else 0)))
{
  var i := 0;
  var total := 0;
  while i < n
    invariant 0 <= i <= n
    invariant total == sum(seq(i, j requires 0 <= j < i => (if j % 11 == 0 || j % 13 == 0 then count7_r(j) else 0)))
  {
    var increment := if i % 11 == 0 || i % 13 == 0 then count7_r(i) else 0;
    total := total + increment;
    i := i + 1;
  }
  result := total;
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