

// <vc-helpers>
function seq<T>(n: nat, f: (i: nat) requires 0 <= i < n -> T) : seq<T>
  decreases n
{
  if n == 0 then [] else seq(n - 1, f) + [f(n - 1)]
}

lemma SumSnoc(s: seq<int>, x: int)
  ensures sum(s + [x]) == sum(s) + x
  decreases |s|
{
  if |s| == 0 {
  } else {
    assert (s + [x])[0] == s[0];
    assert (s + [x])[1..] == s[1..] + [x];
    SumSnoc(s[1..], x);
  }
}

lemma SumSeqExtend(n: nat, f: (i: nat) requires 0 <= i < n + 1 -> int)
  ensures sum(seq(n + 1, f)) ==
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
function seq<T>(n: nat, f: (i: nat) requires 0 <= i < n -> T) : seq<T>
  decreases n
{
  if n == 0 then [] else seq(n - 1, f) + [f(n - 1)]
}

lemma SumSnoc(s: seq<int>, x: int)
  ensures sum(s + [x]) == sum(s) + x
  decreases |s|
{
  if |s| == 0 {
  } else {
    assert (s + [x])[0] == s[0];
    assert (s + [x])[1..] == s[1..] + [x];
    SumSnoc(s[1..], x);
  }
}

lemma SumSeqExtend(n: nat, f: (i: nat) requires 0 <= i < n + 1 -> int)
  ensures sum(seq(n + 1, f)) ==
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