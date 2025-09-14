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
function fizz_buzz_term(i: nat): nat {
  if i % 11 == 0 || i % 13 == 0 then count7_r(i) else 0
}

lemma SumAppend(s: seq<int>, t: seq<int>)
  ensures sum(s + t) == sum(s) + sum(t)
{
  if s != [] {
    SumAppend(s[1..], t);
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
{
  result := 0;
  var i: nat := 0;
  while i < n
    invariant 0 <= i <= n
    invariant result == sum(seq(i, j => fizz_buzz_term(j)))
  {
    SumAppend(seq(i, j => fizz_buzz_term(j)), [fizz_buzz_term(i)]);
    result := result + fizz_buzz_term(i);
    i := i + 1;
  }
}
// </vc-code>
