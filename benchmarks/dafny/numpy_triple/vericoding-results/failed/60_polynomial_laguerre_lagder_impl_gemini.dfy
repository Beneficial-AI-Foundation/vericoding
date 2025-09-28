// <vc-preamble>
// Method to differentiate a Laguerre series
// Helper function for power computation (assumed to exist)
function pow(base: real, exp: nat): real
  decreases exp
{
  if exp == 0 then 1.0
  else base * pow(base, exp - 1)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Replaced recursive Sum with comprehension to fix compilation error. */
function Sum(s: seq<real>, from: nat, to: nat): real
  requires from <= to <= |s|
{
  sum i: nat | from <= i < to :: s[i]
}

/* helper modified by LLM (iteration 2): fixed compilation errors in for loop */
method ComputeLagDerOnce(c: seq<real>) returns (d: seq<real>)
  ensures |d| == |c|
  ensures |c| > 0 ==> d[|c|-1] == 0.0
  ensures |c| > 0 ==> forall i :: 0 <= i < |c|-1 ==> d[i] == -Sum(c, i + 1, |c|)
{
  var n := |c|;
  if n == 0 {
    d := [];
    return;
  }
  var d_arr := new real[n];
  d_arr[n-1] := 0.0;
  var sum := 0.0;
  for i := n-2 downto 0
    invariant -1 <= i <= n-2
    invariant d_arr[n-1] == 0.0
    invariant sum == Sum(c, i + 2, n)
    invariant forall k :: i < k < n-1 ==> d_arr[k] == -Sum(c, k + 1, n)
  {
     sum := sum + c[i+1];
     d_arr[i] := -sum;
  }
  d := d_arr[..];
}
// </vc-helpers>

// <vc-spec>
method {:axiom} LagDer(c: seq<real>, m: nat, scl: real) returns (result: seq<real>)
  requires true
  ensures |result| == |c|
  // If m = 0, no differentiation occurs - result equals input scaled by scl^0 = 1
  ensures m == 0 ==> result == c
  // For over-differentiation (m >= degree + 1), result becomes zero
  ensures m >= |c| && |c| > 0 ==> 
    forall i :: 0 <= i < |result| ==> result[i] == 0.0
  // For main differentiation case (0 < m < |c|), result is scaled by scl^m
  ensures 0 < m < |c| && scl != 0.0 ==> 
    exists base_result: seq<real> :: (|base_result| == |c| &&
    (forall i :: 0 <= i < |result| ==> result[i] == base_result[i] * pow(scl, m)))
  // When scl = 0 and m > 0, result is zero (since scl^m = 0)
  ensures m > 0 && scl == 0.0 ==> 
    forall i :: 0 <= i < |result| ==> result[i] == 0.0
  // Scaling property: differentiating with scl=1 then scaling is equivalent to direct scaling
  ensures m > 0 && |c| > m ==> 
    (forall base: seq<real> :: |base| == |c| ==> 
     forall i :: 0 <= i < |result| ==> result[i] == base[i] * pow(scl, m))
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): No change, fix was in helpers. */
  if |c| == 0 {
    result := [];
    return;
  }

  if m == 0 {
    result := c;
    return;
  }
  
  if m >= |c| {
    result := seq(|c|, _ => 0.0);
    return;
  }

  var temp_c := c;
  var i: nat := 0;
  while i < m
    invariant 0 <= i <= m
    invariant |temp_c| == |c|
    decreases m - i
  {
    var next_c := ComputeLagDerOnce(temp_c);
    temp_c := next_c;
    i := i + 1;
  }
  
  var scale_factor := pow(scl, m);
  result := seq(|c|, k => temp_c[k] * scale_factor);
}
// </vc-code>
