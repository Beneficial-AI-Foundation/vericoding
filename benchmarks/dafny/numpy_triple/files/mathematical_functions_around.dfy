// <vc-preamble>
// Method that rounds each element of a sequence to the given number of decimals
// Helper function for decimal scaling
function pow10(n: int): real
{
  if n == 0 then 1.0
  else if n > 0 then 10.0 * pow10(n-1)
  else 1.0 / pow10(-n)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Around(a: seq<real>, decimals: int := 0) returns (result: seq<real>)
  ensures |result| == |a|
  ensures forall i :: 0 <= i < |a| ==>
    // Zero preservation: rounding zero always produces zero
    (a[i] == 0.0 ==> result[i] == 0.0) &&
    // Order preservation: maintains relative ordering of elements
    (forall j :: 0 <= j < |a| && a[i] <= a[j] ==> result[i] <= result[j]) &&
    // Boundedness: rounded values are within appropriate range of original
    (var scale := pow10(decimals); a[i] - scale <= result[i] <= a[i] + scale) &&
    // Symmetry: non-negative values remain non-negative after rounding
    (a[i] >= 0.0 ==> result[i] >= 0.0)
  // Banker's rounding property: for values exactly halfway between two representable values,
  // rounds to the nearest even number at the specified decimal precision
  ensures forall i :: 0 <= i < |a| ==>
    var scale := pow10(decimals);
    (exists k: int {:trigger k as real} :: a[i] * scale == k as real + 0.5) ==>
    (exists m: int :: result[i] * scale == m as real && m % 2 == 0)
  // Idempotency: rounding an already-rounded value doesn't change it
  ensures forall i :: 0 <= i < |a| ==>
    (var scale := pow10(decimals);
     exists k: int {:trigger k as real} :: a[i] * scale == k as real) ==> result[i] == a[i]
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
