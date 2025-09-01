method fizz_buzz(n: nat) returns (result: nat)
  // post-conditions-start
  ensures result == sum(
    seq(n, i requires 0 <= i < n => (if i % 11 == 0 || i % 13 == 0 then count7_r(i) else 0))
  )
  // post-conditions-end
{
  assume{:axiom} false;
}

// <vc-helpers>
lemma sum_proof(s: seq<int>, i: int)
  requires 0 <= i <= |s|
  ensures sum(s) == sum(s[..i]) + sum(s[i..])
{
  if i == 0 {
    assert s[..0] == [];
    assert s[0..] == s;
  } else if i < |s| {
    sum_proof(s, i-1);
    assert s[..i] == s[..i-1] + [s[i-1]];
    assert s[i..] == [s[i]] + s[i+1..];
    calc {
      sum(s);
      == sum(s[..i]) + sum(s[i..]);
      == {sum_proof(s[..i], i-1)}
      sum(s[..i-1]) + s[i-1] + sum(s[i..]);
      == s[i-1] + sum(s[..i-1]) + sum(s[i..]);
    }
  }
}

lemma sum_empty(s: seq<int>)
  ensures |s| == 0 ==> sum(s) == 0
{
}

lemma sum_single(s: seq<int>)
  requires |s| == 1
  ensures sum(s) == s[0]
{
}

lemma sum_range(s: seq<int>, start: int, end: int)
  requires 0 <= start <= end <= |s|
  ensures sum(s[start..end]) == if start == end then 0 else s[start] + sum(s[start+1..end])
{
  if start < end {
    assert s[start..end] == [s[start]] + s[start+1..end];
  }
}
// </vc-helpers>

// <vc-spec>
method count7(x: nat) returns (count: nat) 
  // post-conditions-start
  ensures count == count7_r(x)
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  result := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant result == sum(seq(n, j requires 0 <= j < i => (if j % 11 == 0 || j % 13 == 0 then count7_r(j) else 0)))
  {
    var add := 0;
    if i % 11 == 0 || i % 13 == 0 {
      add := count7(i);
    }
    result := result + add;
    i := i + 1;
  }
}
// </vc-code>

function count7_r(x: nat): nat {
  var lst := if x % 10 == 7 then 1 else 0;
  if x < 10 then lst else lst + count7_r(x / 10)
}
// pure-end
function sum(s: seq<int>) : int {
  if |s| == 0 then 0 else s[0] + sum(s[1..])
}
// pure-end