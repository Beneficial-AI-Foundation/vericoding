// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method histogram(data: array<real>, bins: array<real>) returns (result: array<int>)
    requires 
        bins.Length >= 2
    ensures
        result.Length == bins.Length - 1
{
    assume {:axiom} false;
}

method histogram_helper(data: array<real>, bins: array<real>, hist: array<int>, index: int) returns (result: array<int>)
    requires 
        bins.Length >= 2 &&
        hist.Length == bins.Length - 1
    ensures
        result.Length == bins.Length - 1
// </vc-spec>
// <vc-code>
{
  result := new int[bins.Length - 1];
  var i := 0;
  while i < result.Length
    invariant 0 <= i <= result.Length
  {
    result[i] := 0;
    i := i + 1;
  }
  
  var j := 0;
  while j < data.Length
    invariant 0 <= j <= data.Length
  {
    var binIndex := 0;
    while binIndex < bins.Length - 1
      invariant 0 <= binIndex <= bins.Length - 1
    {
      if bins[binIndex] <= data[j] < bins[binIndex + 1] {
        result[binIndex] := result[binIndex] + 1;
        break;
      }
      binIndex := binIndex + 1;
    }
    j := j + 1;
  }
}
// </vc-code>
