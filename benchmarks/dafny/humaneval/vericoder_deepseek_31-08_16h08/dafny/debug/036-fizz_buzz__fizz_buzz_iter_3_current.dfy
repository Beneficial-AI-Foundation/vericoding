

// <vc-helpers>
function seq<T>(n: nat, f: nat -> T): seq<T>
  requires n >= 0
  ensures |result| == n
  ensures forall i :: 0 <= i < n ==> result[i] == f(i)
{
  if n == 0 then []
  else seq(n-1, f) + [f(n-1)]
}

lemma seq_property<T>(n: nat, f: nat -> T, i: nat)
  requires 0 <= i < n
  ensures seq(n, f)[i] == f(i)
{
}

lemma sum_concat(s1: seq<int>, s2: seq<int>)
  ensures sum(s1 + s2) == sum(s1) + sum(s2)
{
  if |s1| == 0 {
  } else {
    sum_concat(s1[1..], s2);
  }
}

lemma sum_append(s: seq<int>, x: int)
  ensures sum(s + [x]) == sum(s) + x
{
  sum_concat(s, [x]);
}

function sum(s: seq<int>) : int
  decreases |s|
{
  if |s| == 0 then 0 else s[0] + sum(s[1..])
}

function count7_r(x: nat): nat
  decreases x
{
  if x == 0 then 0
  else if x % 10 == 7 then 1 + count7_r(x / 10)
  else count7_r(x / 10)
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
  var i: nat := 0;
  while i < n
    invariant i <= n
    invariant result == sum(seq(i, (j: nat) => (if j % 11 == 0 || j % 13 == 0 then count7_r(j) else 0)))
  {
    var value := 0;
    if i % 11 == 0 || i % 13 == 0 {
      value := count7_r(i);
    }
    result := result + value;
    i := i + 1;
  }
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