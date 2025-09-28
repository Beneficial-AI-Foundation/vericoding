// <vc-preamble>
// Ghost function for real number exponentiation with natural number exponents
ghost function Pow(base: real, exp: nat): real
    decreases exp
{
    if exp == 0 then 1.0
    else base * Pow(base, exp - 1)
}

// Generate a Vandermonde matrix with decreasing powers (default behavior)
// The Vandermonde matrix is a matrix with terms of a geometric progression in each row
// For input vector x of length n and m columns, entry (i,j) = x[i]^(m-1-j)
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): no changes needed, function is correct */
function Power(base: real, exp: nat): real 
    decreases exp
{
    if exp == 0 then 1.0
    else base * Power(base, exp - 1)
}

/* helper modified by LLM (iteration 5): no changes needed, lemma is correct */
lemma PowerIsPow(base: real, exp: nat)
    ensures Power(base, exp) == Pow(base, exp)
    decreases exp
{
    if exp > 0 {
        PowerIsPow(base, exp - 1);
    }
}
// </vc-helpers>

// <vc-spec>
method Vander(x: seq<real>, m: nat) returns (result: seq<seq<real>>)
    requires m > 0
    ensures |result| == |x|
    ensures forall i :: 0 <= i < |result| ==> |result[i]| == m
    ensures forall i, j :: 0 <= i < |x| && 0 <= j < m ==> 
            result[i][j] == Pow(x[i], (m - 1 - j) as nat)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): combined two loop invariants to provide a trigger for the quantifier */
  var res: seq<seq<real>> := [];
  var i := 0;
  while i < |x|
    invariant |res| == i
    invariant 0 <= i <= |x|
    invariant forall k :: 0 <= k < i ==> |res[k]| == m
    invariant forall k, j :: 0 <= k < i && 0 <= j < m ==> res[k][j] == Pow(x[k], (m - 1 - j) as nat)
  {
    var row: seq<real> := [];
    var j := 0;
    while j < m
      invariant |row| == j
      invariant 0 <= j <= m
      invariant forall l :: 0 <= l < j ==> m - 1 - l >= 0 && row[l] == Pow(x[i], (m - 1 - l) as nat)
    {
      var exp := m - 1 - j;
      assert exp >= 0;
      var p := Power(x[i], exp as nat);
      PowerIsPow(x[i], exp as nat);
      row := row + [p];
      j := j + 1;
    }
    res := res + [row];
    i := i + 1;
  }
  result := res;
}
// </vc-code>
