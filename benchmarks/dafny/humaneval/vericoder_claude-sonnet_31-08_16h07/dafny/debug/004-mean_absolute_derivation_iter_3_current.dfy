function sum(s: seq<real>) : real {
  if |s| == 0 then 0.0 else s[0] + sum(s[1..])
}
function abs(x: real) : real
  ensures abs(x) >= 0.0
{
  if x >= 0.0 then x else -x
}
function mean(s: seq<real>) : real
  requires |s| > 0
{
  sum(s) / |s| as real
}

// <vc-helpers>
lemma sum_seq_constructor(s: seq<real>, f: int -> real)
  requires |s| == |seq(|s|, i requires 0 <= i < |s| => f(i))|
  ensures sum(s) == sum(seq(|s|, i requires 0 <= i < |s| => f(i))) ==> s == seq(|s|, i requires 0 <= i < |s| => f(i))
{
}

lemma mean_seq_constructor(s: seq<real>)
  requires |s| > 0
  ensures mean(s) == sum(s) / |s| as real
{
}

lemma mean_absolute_derivation_correctness(numbers: seq<real>)
  requires |numbers| > 0
  ensures var m := mean(numbers);
          var deviations := seq(|numbers|, i requires 0 <= i < |numbers| => abs(numbers[i] - m));
          mean(deviations) == mean(seq(|numbers|, i requires 0 <= i < |numbers| => abs(numbers[i] - m)))
{
  var m := mean(numbers);
  var deviations := seq(|numbers|, i requires 0 <= i < |numbers| => abs(numbers[i] - m));
  var expected := seq(|numbers|, i requires 0 <= i < |numbers| => abs(numbers[i] - m));
  
  assert deviations == expected;
  assert mean(deviations) == mean(expected);
}
// </vc-helpers>

// <vc-spec>
method mean_absolute_derivation(numbers: seq<real>) returns (derivation: real)
  // pre-conditions-start
  requires |numbers| > 0
  // pre-conditions-end
  // post-conditions-start
  ensures var m := mean(numbers);
    derivation == mean(seq(|numbers|, i requires 0 <= i < |numbers| => abs(numbers[i] - m)))
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var m := mean(numbers);
  var deviations := seq(|numbers|, i requires 0 <= i < |numbers| => abs(numbers[i] - m));
  derivation := mean(deviations);
  
  mean_absolute_derivation_correctness(numbers);
}
// </vc-code>

