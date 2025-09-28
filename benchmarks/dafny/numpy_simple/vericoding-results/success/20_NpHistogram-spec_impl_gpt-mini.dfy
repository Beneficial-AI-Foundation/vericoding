// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): added reads clauses and fixed comparisons */
function FindBin(x: real, bins: array<real>, i: int): int
  requires 0 <= i <= bins.Length - 1
  reads bins
  decreases bins.Length - i
{
  if i == bins.Length - 1 then -1
  else if bins[i] <= x && x < bins[i+1] then i
  else FindBin(x, bins, i+1)
}

/* helper modified by LLM (iteration 2): added reads clause */
function find_bin(x: real, bins: array<real>): int
  requires bins.Length >= 2
  reads bins
{
  FindBin(x, bins, 0)
}
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
  /* code modified by LLM (iteration 2): clamp start index and accumulate histogram */
  var res := new int[bins.Length - 1];
  var i := 0;
  while i < hist.Length
    invariant 0 <= i <= hist.Length
    invariant res.Length == hist.Length
    decreases hist.Length - i
  {
    res[i] := hist[i];
    i := i + 1;
  }
  var j := if 0 <= index && index <= data.Length then index else 0;
  while j < data.Length
    invariant 0 <= j <= data.Length
    invariant res.Length == bins.Length - 1
    decreases data.Length - j
  {
    var v := data[j];
    var b := find_bin(v, bins);
    if 0 <= b && b < res.Length {
      res[b] := res[b] + 1;
    }
    j := j + 1;
  }
  result := res;
}
// </vc-code>
