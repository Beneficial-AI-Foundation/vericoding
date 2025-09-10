predicate ValidInput(n: nat, m: nat, benches: seq<nat>)
{
    n > 0 && m > 0 && |benches| == n && forall i :: 0 <= i < n ==> benches[i] > 0
}

function max_seq(s: seq<nat>): nat
    requires |s| > 0
{
    if |s| == 1 then s[0]
    else if s[0] >= max_seq(s[1..]) then s[0]
    else max_seq(s[1..])
}

function sum_seq(s: seq<nat>): nat
{
    if |s| == 0 then 0
    else s[0] + sum_seq(s[1..])
}

// <vc-helpers>
lemma max_seq_properties(s: seq<nat>, i: int)
  requires |s| > 0
  requires 0 <= i < |s|
  ensures max_seq(s) >= s[i]
{
  if |s| == 1 {
    assert i == 0;
  } else {
    if i == 0 {
      if s[0] >= max_seq(s[1..]) {
      } else {
        assert max_seq(s) == max_seq(s[1..]);
        max_seq_properties(s[1..], i);
      }
    } else {
      max_seq_properties(s[1..], i-1);
    }
  }
}

lemma sum_seq_positive(s: seq<nat>)
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> s[i] > 0
  ensures sum_seq(s) > 0
{
  if |s| == 1 {
  } else {
    sum_seq_positive(s[1..]);
  }
}

lemma sum_seq_bound(s: seq<nat>)
  requires |s| > 0
  requires forall i :: 0 <= i < |s| ==> s[i] > 0
  ensures sum_seq(s) >= |s|
{
  if |s| == 1 {
    assert sum_seq(s) == s[0] > 0;
  } else {
    sum_seq_bound(s[1..]);
  }
}

lemma division_lemma(a: nat, b: nat)
  requires b > 0
  ensures (a + b - 1) / b == if a % b == 0 then a / b else a / b + 1
{
  if a % b == 0 {
    assert a % b == 0;
    assert a == b * (a / b);
    calc {
      (a + b - 1) / b;
      (b * (a / b) + b - 1) / b;
      (a / b) + (b - 1) / b;
      (a / b) + 0;
      a / b;
    }
  } else {
    var q := a / b;
    var r := a % b;
    assert a == b * q + r && 0 < r < b;
    calc {
      (a + b - 1) / b;
      (b * q + r + b - 1) / b;
      q + (r + b - 1) / b;
      q + 1;
    }
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: nat, m: nat, benches: seq<nat>) returns (minimum: nat, maximum: nat)
    requires ValidInput(n, m, benches)
    ensures maximum == max_seq(benches) + m
    ensures var total := sum_seq(benches) + m;
            var current_max := max_seq(benches);
            if total <= current_max * n then minimum == current_max
            else minimum == (total + n - 1) / n
// </vc-spec>
// <vc-code>
{
  maximum := max_seq(benches) + m;
  var total := sum_seq(benches) + m;
  var current_max := max_seq(benches);
  
  if total <= current_max * n {
    minimum := current_max;
  } else {
    division_lemma(total, n);
    minimum := (total + n - 1) / n;
  }
}
// </vc-code>

