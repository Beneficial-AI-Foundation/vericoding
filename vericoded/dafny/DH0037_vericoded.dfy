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
function fizz_buzz_seq(n: nat): seq<int>
{
  seq(n, i requires 0 <= i < n => (if i % 11 == 0 || i % 13 == 0 then count7_r(i) as int else 0))
}

/* helper modified by LLM (iteration 3): Added cast to int for count7_r result */
lemma sum_append(s: seq<int>, x: int)
  ensures sum(s + [x]) == sum(s) + x
{
  if |s| == 0 {
    assert s + [x] == [x];
    assert sum([x]) == x;
  } else {
    assert (s + [x])[0] == s[0];
    assert (s + [x])[1..] == s[1..] + [x];
  }
}

/* helper modified by LLM (iteration 3): Simplified to work with sequence extension */
lemma sum_extend(n: nat)
  ensures n > 0 ==> sum(seq(n, i requires 0 <= i < n => (if i % 11 == 0 || i % 13 == 0 then count7_r(i) as int else 0))) ==
                    sum(seq(n-1, i requires 0 <= i < n-1 => (if i % 11 == 0 || i % 13 == 0 then count7_r(i) as int else 0))) +
                    (if (n-1) % 11 == 0 || (n-1) % 13 == 0 then count7_r(n-1) as int else 0)
{
  if n > 0 {
    var s := seq(n-1, i requires 0 <= i < n-1 => (if i % 11 == 0 || i % 13 == 0 then count7_r(i) as int else 0));
    var full := seq(n, i requires 0 <= i < n => (if i % 11 == 0 || i % 13 == 0 then count7_r(i) as int else 0));
    var last_val := if (n-1) % 11 == 0 || (n-1) % 13 == 0 then count7_r(n-1) as int else 0;
    assert |full| == n;
    assert |s| == n-1;
    assert full == s + [last_val];
    sum_append(s, last_val);
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
  /* code modified by LLM (iteration 3): Use sum_extend lemma to maintain invariant properly */
  result := 0;
  var i: nat := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant result == sum(seq(i, j requires 0 <= j < i => (if j % 11 == 0 || j % 13 == 0 then count7_r(j) as int else 0)))
  {
    sum_extend(i+1);
    
    if i % 11 == 0 || i % 13 == 0 {
      result := result + count7_r(i);
    }
    
    i := i + 1;
  }
}
// </vc-code>
