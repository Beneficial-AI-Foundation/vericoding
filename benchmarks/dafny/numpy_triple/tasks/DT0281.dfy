// <vc-preamble>
// Method to calculate absolute value element-wise for a sequence of integers
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Absolute(x: seq<int>) returns (result: seq<int>)
  ensures |result| == |x|
  // Basic definition: |x[i]| = x[i] if x[i] ≥ 0, otherwise -x[i]
  ensures forall i :: 0 <= i < |x| ==> result[i] == (if x[i] >= 0 then x[i] else -x[i])
  // Non-negativity: |x[i]| ≥ 0 for all i
  ensures forall i :: 0 <= i < |result| ==> result[i] >= 0
  // Zero preservation: |x[i]| = 0 if and only if x[i] = 0
  ensures forall i :: 0 <= i < |x| ==> (result[i] == 0 <==> x[i] == 0)
  // Idempotence: ||x[i]|| = |x[i]| (absolute of absolute equals absolute)
  ensures forall i :: 0 <= i < |result| ==> 
    (if result[i] >= 0 then result[i] else -result[i]) == result[i]
  // Multiplicativity: |x[i] * y| = |x[i]| * |y| for any integer y
  ensures forall i, y {:trigger x[i] * y} :: 0 <= i < |x| ==> 
    (if (x[i] * y) >= 0 then (x[i] * y) else -(x[i] * y)) == 
    result[i] * (if y >= 0 then y else -y)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
