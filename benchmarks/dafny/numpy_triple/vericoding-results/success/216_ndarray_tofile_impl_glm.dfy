// <vc-preamble>
// Float type to match Lean specification
type Float = real
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method NumpyToFile(arr: seq<Float>, filename: string, n: nat)
  // Array length must match the specified size parameter
  requires |arr| == n
  
  // Postconditions: Operation succeeds and preserves data properties
  // - File data length equals array length (n)
  // - Exact values preserved in sequential order
  // - No precision loss occurs
  // - Data stored in 'C' order (row-major) format
  ensures true  // Operation completes successfully (equivalent to result = () in Lean)
// </vc-spec>
// <vc-code>
{
  var i := 0;
  while i < n
    invariant 0 <= i <= n
  {
    // Process each element sequentially (C-order)
    i := i + 1;
  }
}
// </vc-code>
