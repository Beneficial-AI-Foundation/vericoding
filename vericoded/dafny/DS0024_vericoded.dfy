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
  var hist := new int[bins.Length - 1];
  var i := 0;
  while i < hist.Length
  {
    hist[i] := 0;
    i := i + 1;
  }
  
  var j := 0;
  while j < data.Length
  {
    var k := 0;
    while k < bins.Length - 1
    {
      if bins[k] <= data[j] && data[j] < bins[k + 1] {
        hist[k] := hist[k] + 1;
        break;
      }
      k := k + 1;
    }
    j := j + 1;
  }
  
  result := hist;
}
// </vc-code>
