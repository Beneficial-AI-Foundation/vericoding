// <vc-preamble>
// Power function for real numbers (assumed to exist or be provided by library)
function pow(base: real, exponent: real): real
  requires base > 0.0
{
  1.0  // Placeholder implementation for compilation
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method logspace(start: real, stop: real, endpoint: bool, base: real, num: nat)
  returns (result: seq<real>)
  // Preconditions: base must be positive and not equal to 1, num must be positive
  requires base > 0.0
  requires base != 1.0
  requires num > 0
  // Postconditions specify the logarithmic spacing behavior
  ensures |result| == num
  ensures
    // Define step size based on endpoint parameter
    var step := if endpoint && num > 1 then (stop - start) / (num - 1) as real
                else (stop - start) / num as real;
    // Each element follows the logarithmic spacing formula: base^(start + i * step)
    forall i :: 0 <= i < num ==> result[i] == pow(base, start + (i as real) * step)
  ensures
    // First element is always base^start
    result[0] == pow(base, start)
  ensures
    // Last element is base^stop when endpoint is true and num > 1
    (endpoint && num > 1) ==> result[num - 1] == pow(base, stop)
  ensures
    // All elements are positive since base is positive
    forall i :: 0 <= i < num ==> result[i] > 0.0
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 4): fixed duplicate variable name by assigning to return result directly instead of declaring a local var */
  var step := if endpoint && num > 1 then (stop - start) / (num - 1) as real
              else (stop - start) / num as real;
  result := [];
  var i := 0;
  while i < num
    invariant 0 <= i <= num
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] == pow(base, start + (j as real) * step)
  {
    result := result + [pow(base, start + (i as real) * step)];
    i := i + 1;
  }
}
// </vc-code>
