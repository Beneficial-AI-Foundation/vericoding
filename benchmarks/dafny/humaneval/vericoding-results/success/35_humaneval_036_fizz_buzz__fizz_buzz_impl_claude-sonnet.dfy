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
/* helper modified by LLM (iteration 2): added lemma to prove sum extension property */
lemma sum_extension(s: seq<int>, x: int)
  ensures sum(s + [x]) == sum(s) + x
{
  if |s| == 0 {
    assert s + [x] == [x];
    assert sum([x]) == x;
    assert sum(s) == 0;
  } else {
    assert s + [x] == [s[0]] + (s[1..] + [x]);
    sum_extension(s[1..], x);
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
  /* code modified by LLM (iteration 2): fixed loop invariant maintenance using sum extension lemma */
  result := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant result == sum(seq(i, j requires 0 <= j < i => (if j % 11 == 0 || j % 13 == 0 then count7_r(j) else 0)))
  {
    var current_value := if i % 11 == 0 || i % 13 == 0 then count7_r(i) else 0;
    var old_seq := seq(i, j requires 0 <= j < i => (if j % 11 == 0 || j % 13 == 0 then count7_r(j) else 0));
    var new_seq := seq(i + 1, j requires 0 <= j < i + 1 => (if j % 11 == 0 || j % 13 == 0 then count7_r(j) else 0));
    
    assert new_seq == old_seq + [current_value];
    sum_extension(old_seq, current_value);
    
    result := result + current_value;
    i := i + 1;
  }
}
// </vc-code>
