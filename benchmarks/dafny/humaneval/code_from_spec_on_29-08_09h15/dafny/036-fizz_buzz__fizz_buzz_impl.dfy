

// <vc-helpers>
lemma SumProperty(s: seq<int>, i: nat)
  requires i < |s|
  ensures sum(s) == sum(s[..i]) + s[i] + sum(s[i+1..])
{
  if i == 0 {
    assert s[..0] == [];
    assert s[0+1..] == s[1..];
    assert sum(s[..0]) == sum([]) == 0;
    assert s == [s[0]] + s[1..];
    SumConcat([s[0]], s[1..]);
  } else {
    assert s == [s[0]] + s[1..];
    assert s[..i] == [s[0]] + s[1..][..i-1];
    assert s[i] == s[1..][i-1];
    assert s[i+1..] == s[1..][i-1+1..];
    SumProperty(s[1..], i-1);
    SumConcat([s[0]], s[1..][..i-1]);
  }
}

lemma SumEmpty()
  ensures sum([]) == 0
{
}

lemma SumSingle(x: int)
  ensures sum([x]) == x
{
}

lemma SumConcat(s1: seq<int>, s2: seq<int>)
  ensures sum(s1 + s2) == sum(s1) + sum(s2)
{
  if |s1| == 0 {
    assert s1 + s2 == s2;
    assert sum(s1) == 0;
  } else {
    assert s1 + s2 == [s1[0]] + (s1[1..] + s2);
    SumConcat(s1[1..], s2);
    assert sum(s1 + s2) == s1[0] + sum(s1[1..] + s2);
    assert sum(s1[1..] + s2) == sum(s1[1..]) + sum(s2);
    assert sum(s1) == s1[0] + sum(s1[1..]);
  }
}
// </vc-helpers>

// <vc-description>
/*
function_signature: method fizz_buzz(n: nat) returns (result: nat)
Process input. Requires: returns the correct size/count. Ensures: returns the correct value.
*/
// </vc-description>

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
  
  while i < n
    invariant 0 <= i <= n
    invariant result == sum(seq(i, j requires 0 <= j < i => (if j % 11 == 0 || j % 13 == 0 then count7_r(j) else 0)))
  {
    if i % 11 == 0 || i % 13 == 0 {
      var count := count7(i);
      result := result + count;
    }
    i := i + 1;
    
    ghost var prev_seq := seq(i-1, j requires 0 <= j < i-1 => (if j % 11 == 0 || j % 13 == 0 then count7_r(j) else 0));
    ghost var curr_seq := seq(i, j requires 0 <= j < i => (if j % 11 == 0 || j % 13 == 0 then count7_r(j) else 0));
    assert curr_seq == prev_seq + [if (i-1) % 11 == 0 || (i-1) % 13 == 0 then count7_r(i-1) else 0];
    SumConcat(prev_seq, [if (i-1) % 11 == 0 || (i-1) % 13 == 0 then count7_r(i-1) else 0]);
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