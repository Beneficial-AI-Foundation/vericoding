//ATOM
// Given an array of integers, it returns the sum. [1,3,3,2]->9

function Sum(xs: seq<int>): int {
  if |xs| == 0 then 0 else Sum(xs[..|xs|-1]) + xs[|xs|-1]
}


// SPEC

method SumArray(xs: array<int>) returns (s: int)
  ensures s == Sum(xs[..])
{
}
