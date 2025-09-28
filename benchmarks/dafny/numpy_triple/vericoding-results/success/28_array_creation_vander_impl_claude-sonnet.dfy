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
/* helper modified by LLM (iteration 4): added lemma to establish equivalence between Pow and Power */
function Power(base: real, exp: nat): real
    decreases exp
{
    if exp == 0 then 1.0
    else base * Power(base, exp - 1)
}

lemma PowerEqualsPow(base: real, exp: nat)
    ensures Power(base, exp) == Pow(base, exp)
{
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
  /* code modified by LLM (iteration 4): added explicit trigger to fix warning */
  result := [];
  var i := 0;
  while i < |x|
    invariant 0 <= i <= |x|
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> |result[k]| == m
    invariant forall k, j :: 0 <= k < i && 0 <= j < m ==> result[k][j] == Power(x[k], (m - 1 - j) as nat)
  {
    var row := [];
    var j := 0;
    while j < m
      invariant 0 <= j <= m
      invariant |row| == j
      invariant forall l :: 0 <= l < j ==> row[l] == Power(x[i], (m - 1 - l) as nat)
    {
      row := row + [Power(x[i], (m - 1 - j) as nat)];
      j := j + 1;
    }
    result := result + [row];
    i := i + 1;
  }
  
  forall i, j | 0 <= i < |x| && 0 <= j < m
    ensures result[i][j] == Pow(x[i], (m - 1 - j) as nat)
  {
    PowerEqualsPow(x[i], (m - 1 - j) as nat);
  }
}
// </vc-code>
