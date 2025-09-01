

// <vc-helpers>
lemma sum_property(s: seq<int>, i: int)
  requires 0 <= i < |s|
  ensures sum(s[..i+1]) == sum(s[..i]) + s[i]
{
  if i == 0 {
    assert s[..1] == [s[0]];
    assert s[..0] == [];
  } else {
    assert s[..i+1] == s[..i] + [s[i]];
    sum_append_single(s[..i], s[i]);
  }
}

lemma sum_append_single(s: seq<int>, x: int)
  ensures sum(s + [x]) == sum(s) + x
{
  if |s| == 0 {
    assert s + [x] == [x];
  } else {
    assert s + [x] == [s[0]] + s[1..] + [x];
    assert s + [x] == [s[0]] + (s[1..] + [x]);
    sum_append_single(s[1..], x);
  }
}

lemma sum_zero_prefix(n: nat, i: nat)
  requires i <= n
  ensures sum(seq(i, j requires 0 <= j < i => (if j % 11 == 0 || j % 13 == 0 then count7_r(j) else 0))) 
          + (if i < n && (i % 11 == 0 || i % 13 == 0) then count7_r(i) else 0)
          == sum(seq(i+1, j requires 0 <= j < i+1 => (if j % 11 == 0 || j % 13 == 0 then count7_r(j) else 0)))
{
  if i == 0 {
    // Base case
  } else {
    // The sequences differ only in the last element
    var s1 := seq(i, j requires 0 <= j < i => (if j % 11 == 0 || j % 13 == 0 then count7_r(j) else 0));
    var s2 := seq(i+1, j requires 0 <= j < i+1 => (if j % 11 == 0 || j % 13 == 0 then count7_r(j) else 0));
    
    if i < n {
      assert |s2| == i + 1;
      assert |s1| == i;
      assert s2[i] == (if i % 11 == 0 || i % 13 == 0 then count7_r(i) else 0);
    }
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
  
  while i < n
    invariant 0 <= i <= n
    invariant result == sum(seq(i, j requires 0 <= j < i => (if j % 11 == 0 || j % 13 == 0 then count7_r(j) else 0)))
  {
    if i % 11 == 0 || i % 13 == 0 {
      var count := count7(i);
      result := result + count;
    }
    
    sum_zero_prefix(n, i);
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