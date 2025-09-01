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
lemma sum_abs_diff(s: seq<real>, m: real)
  ensures sum(seq(|s|, i requires 0 <= i < |s| => abs(s[i] - m))) ==
          sum(seq(|s|, i requires 0 <= i < |s| => if s[i] >= m then s[i] - m else m - s[i]))
{
}

lemma sum_split(s: seq<real>, m: real)
  ensures sum(seq(|s|, i requires 0 <= i < |s| => s[i] - m)) == sum(s) - |s| as real * m
{
}

lemma mean_property(s: seq<real>)
  requires |s| > 0
  ensures mean(s) == sum(s) / |s| as real
{
}

lemma abs_triangle(x: real, y: real)
  ensures abs(x + y) <= abs(x) + abs(y)
{
}

lemma abs_neg(x: real)
  ensures abs(-x) == abs(x)
{
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
  var n := |numbers|;
  var total := 0.0;
  var i := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant total == sum(seq(i, j requires 0 <= j < i => abs(numbers[j] - m)))
  {
    total := total + abs(numbers[i] - m);
    i := i + 1;
  }
  
  derivation := total / n as real;
}
// </vc-code>

