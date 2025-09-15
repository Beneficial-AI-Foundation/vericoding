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
/* helper modified by LLM (iteration 2): lemma to prove sum of non-negative sequence is non-negative */
lemma SeqSumNonNegative(s: seq<int>)
  requires forall i :: 0 <= i < |s| ==> s[i] >= 0
  ensures sum(s) >= 0
{
  if |s| == 0 {
  } else {
    SeqSumNonNegative(s[1..]);
    calc {
      sum(s);
      s[0] + sum(s[1..]);
    }
    assert s[0] >= 0;
    assert sum(s[1..]) >= 0;
    assert s[0] + sum(s[1..]) >= 0;
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
/* code modified by LLM (iteration 2): fix type issues and add lemma call */
{
  var s: seq<int> := seq(n, i requires 0 <= i < n => 
    if i % 11 == 0 || i % 13 == 0 then count7_r(i) else 0
  );
  SeqSumNonNegative(s);
  result := sum(s) as nat;
}
// </vc-code>
