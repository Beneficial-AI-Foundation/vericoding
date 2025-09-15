

// <vc-helpers>
lemma sum_prop(s: seq<int>)
  requires |s| > 0
  ensures sum(s) == sum(s[..|s|-1]) + s[|s|-1]
{
  if |s| == 1 {
    assert s[..|s|-1] == s[..0] == [];
    assert sum(s) == s[0] + sum(s[1..]) == s[0] + sum([]) == s[0] + 0 == s[0];
    assert sum(s[..|s|-1]) + s[|s|-1] == sum([]) + s[0] == 0 + s[0] == s[0];
  } else {
    assert s == s[0..1] + s[1..];
    assert sum(s) == s[0] + sum(s[1..]);
    assert s[1..][..|s[1..]|-1] == s[1..|s|-1];
    sum_prop(s[1..]);
    assert sum(s[1..]) == sum(s[1..|s|-1]) + s[|s|-1];
    assert s[..|s|-1] == s[0..1] + s[1..|s|-1];
    assert sum(s[..|s|-1]) == s[0] + sum(s[1..|s|-1]);
    assert sum(s) == s[0] + sum(s[1..|s|-1]) + s[|s|-1];
    assert sum(s) == sum(s[..|s|-1]) + s[|s|-1];
  }
}

lemma sum_empty()
  ensures sum([]) == 0
{
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
  ghost var s := [];
  
  while i < n
    invariant 0 <= i <= n
    invariant |s| == i
    invariant s == seq(i, j requires 0 <= j < i => (if j % 11 == 0 || j % 13 == 0 then count7_r(j) else 0))
    invariant result == sum(s)
  {
    var val := 0;
    if i % 11 == 0 || i % 13 == 0 {
      val := count7(i);
    }
    
    ghost var s_old := s;
    s := s + [val];
    
    assert s[..|s|-1] == s_old;
    assert s[|s|-1] == val;
    
    if |s| > 0 {
      sum_prop(s);
    }
    
    result := result + val;
    i := i + 1;
  }
  
  assert s == seq(n, j requires 0 <= j < n => (if j % 11 == 0 || j % 13 == 0 then count7_r(j) else 0));
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