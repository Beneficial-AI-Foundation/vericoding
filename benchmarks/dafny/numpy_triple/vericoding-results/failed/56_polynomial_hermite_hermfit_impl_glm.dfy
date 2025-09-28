// <vc-preamble>
// Helper function to evaluate a Hermite polynomial at a point
// This is a mathematical specification of Hermite polynomial evaluation
ghost function HermitePolynomial(k: nat, x: real): real
  decreases k
{
  if k == 0 then 1.0
  else if k == 1 then 2.0 * x
  else 2.0 * x * HermitePolynomial(k-1, x) - 2.0 * (k-1) as real * HermitePolynomial(k-2, x)
}

// Evaluate a Hermite series with given coefficients at a point
ghost function EvaluateHermiteSeries(coeffs: seq<real>, x: real): real
  requires |coeffs| > 0
{
  EvaluateHermiteSeriesHelper(coeffs, x, 0)
}

ghost function EvaluateHermiteSeriesHelper(coeffs: seq<real>, x: real, i: nat): real
  requires |coeffs| > 0
  requires i <= |coeffs|
  decreases |coeffs| - i
{
  if i == |coeffs| then 0.0
  else coeffs[i] * HermitePolynomial(i, x) + EvaluateHermiteSeriesHelper(coeffs, x, i+1)
}

// Calculate sum of squared errors for given coefficients
ghost function SumSquaredError(x_vals: seq<real>, y_vals: seq<real>, coeffs: seq<real>): real
  requires |x_vals| == |y_vals|
  requires |x_vals| > 0
  requires |coeffs| > 0
{
  SumSquaredErrorHelper(x_vals, y_vals, coeffs, 0)
}

ghost function SumSquaredErrorHelper(x_vals: seq<real>, y_vals: seq<real>, coeffs: seq<real>, i: nat): real
  requires |x_vals| == |y_vals|
  requires |coeffs| > 0
  requires i <= |x_vals|
  decreases |x_vals| - i
{
  if i == |x_vals| then 0.0
  else
    var predicted := EvaluateHermiteSeries(coeffs, x_vals[i]);
    var error := y_vals[i] - predicted;
    error * error + SumSquaredErrorHelper(x_vals, y_vals, coeffs, i+1)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): removed array2 constructor calls in expressions */
function SwapRows(matrix: array2<real>, row1: int, row2: int): array2<real>
  requires 0 <= row1 < matrix.Length0
  requires 0 <= row2 < matrix.Length0
  requires 0 < matrix.Length1
{
  if row1 == row2 then matrix
  else
    var new_matrix: array2<real> := new array2<real>(matrix.Length0, matrix.Length1);
    for i := 0 to matrix.Length0
      invariant 0 <= i <= matrix.Length0
    {
      for j := 0 to matrix.Length1
        invariant 0 <= j <= matrix.Length1
      {
        if i == row1 then
          new_matrix[i, j] := matrix[row2, j];
        else if i == row2 then
          new_matrix[i, j] := matrix[row1, j];
        else
          new_matrix[i, j] := matrix[i, j];
      }
    }
    new_matrix
}

function SwapElements(arr: array<real>, i: int, j: int): array<real>
  requires 0 <= i < arr.Length
  requires 0 <= j < arr.Length
{
  if i == j then arr
  else
    var new_arr: array<real> := new real[arr.Length];
    for k := 0 to arr.Length
      invariant 0 <= k <= arr.Length
    {
      if k == i then
        new_arr[k] := arr[j];
      else if k == j then
        new_arr[k] := arr[i];
      else
        new_arr[k] := arr[k];
    }
    new_arr
}
// </vc-helpers>

// <vc-spec>
method hermfit(x: seq<real>, y: seq<real>, deg: nat) returns (coeff: seq<real>)
  requires |x| == |y|
  requires |x| > 0
  requires deg >= 0
  
  ensures |coeff| == deg + 1
  ensures deg + 1 > 0
  
  // Least squares optimality property: the returned coefficients minimize
  // the sum of squared errors compared to any other coefficient vector
  ensures forall other_coeffs: seq<real> :: 
    |other_coeffs| == deg + 1 ==>
    SumSquaredError(x, y, coeff) <= SumSquaredError(x, y, other_coeffs)
  
  // For interpolation case: when number of points equals degree + 1,
  // and points are distinct, the polynomial passes through all points exactly
  ensures |x| == deg + 1 && (forall i, j :: 0 <= i < j < |x| ==> x[i] != x[j]) ==>
    forall i :: 0 <= i < |x| ==> EvaluateHermiteSeries(coeff, x[i]) == y[i]
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): fixed matrix creation to avoid constructor calls in expressions */
  // Initialize coefficients to zero
  coeff := new real[deg + 1];
  
  // For the interpolation case (|x| == deg + 1), solve the linear system
  if |x| == deg + 1 {
    // Build the Vandermonde-like matrix for Hermite polynomials
    var matrix: array2<real> := new array2<real>(deg + 1, deg + 1);
    
    // Create a mutable copy of y
    var y_arr := new real[|y|];
    for i := 0 to |y|
      invariant 0 <= i <= |y|
      invariant forall j :: 0 <= j < i ==> y_arr[j] == y[j]
    {
      if i < |y| {
        y_arr[i] := y[i];
      }
    }
    
    // Fill the matrix with Hermite polynomial values
    for i := 0 to |x|
      invariant 0 <= i <= |x|
    {
      if i < |x| {
        for j := 0 to deg + 1
          invariant 0 <= j <= deg + 1
          invariant forall k :: 0 <= k < j ==> matrix[i, k] == HermitePolynomial(k, x[i])
        {
          if j < deg + 1 {
            matrix[i, j] := HermitePolynomial(j, x[i]);
          }
        }
      }
    }
    
    // Solve the linear system matrix * coeff = y_arr
    // Using Gaussian elimination (simplified for this context)
    
    // Forward elimination
    for k := 0 to deg
      invariant 0 <= k <= deg
    {
      // Find pivot
      var pivot := k;
      for i := k + 1 to deg
        invariant k + 1 <= i <= deg
      {
        if i < matrix.Length0 && |matrix[i, k]| > |matrix[pivot, k]| {
          pivot := i;
        }
      }
      
      // Swap rows if needed
      if pivot != k {
        matrix := SwapRows(matrix, k, pivot);
        y_arr := SwapElements(y_arr, k, pivot);
      }
      
      // Eliminate column
      for i := k + 1 to deg
        invariant k + 1 <= i <= deg
      {
        if i < matrix.Length0 && k < matrix.Length1 {
          var factor := matrix[i, k] / matrix[k, k];
          for j := k to deg
            invariant k <= j <= deg
          {
            if j < matrix.Length1 {
              matrix[i, j] := matrix[i, j] - factor * matrix[k, j];
            }
          }
          if i < y_arr.Length && k < y_arr.Length {
            y_arr[i] := y_arr[i] - factor * y_arr[k];
          }
        }
      }
    }
    
    // Back substitution
    for i := deg downto 0
      invariant 0 <= i <= deg
    {
      if i < coeff.Length && i < y_arr.Length {
        coeff[i] := y_arr[i];
        for j := i + 1 to deg
          invariant i + 1 <= j <= deg
        {
          if j < coeff.Length && i < matrix.Length0 && j < matrix.Length1 {
            coeff[i] := coeff[i] - matrix[i, j] * coeff[j];
          }
        }
        if i < matrix.Length0 && i < matrix.Length1 && matrix[i, i] != 0.0 {
          coeff[i] := coeff[i] / matrix[i, i];
        }
      }
    }
  } else {
    // For the least squares case (|x| > deg + 1), use gradient descent
    // Initialize with small random values (simplified to zeros here)
    for i := 0 to deg + 1
      invariant 0 <= i <= deg + 1
    {
      if i < coeff.Length {
        coeff[i] := 0.0;
      }
    }
    
    // Gradient descent to minimize sum of squared errors
    var learning_rate := 0.01;
    var iterations := 1000;
    
    for iter := 0 to iterations
      invariant 0 <= iter <= iterations
    {
      var new_coeff := new real[deg + 1];
      
      // Compute gradient and update coefficients
      for j := 0 to deg + 1
        invariant 0 <= j <= deg + 1
      {
        if j < new_coeff.Length && j < coeff.Length {
          var grad := Gradient(x, y, coeff, j);
          new_coeff[j] := coeff[j] - learning_rate * grad;
        }
      }
      
      // Update coefficients
      coeff := new_coeff;
    }
  }
}
// </vc-code>
