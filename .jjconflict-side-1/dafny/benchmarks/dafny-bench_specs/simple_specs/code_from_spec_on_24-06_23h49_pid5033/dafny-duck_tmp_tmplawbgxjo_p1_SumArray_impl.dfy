//ATOM
// Given an array of integers, it returns the sum. [1,3,3,2]->9

function Sum(xs: seq<int>): int {
  if |xs| == 0 then 0 else Sum(xs[..|xs|-1]) + xs[|xs|-1]
}

/* code modified by LLM (iteration 4): Added helper lemma to prove Sum property for sequences */
lemma SumProperty(xs: seq<int>, i: int)
  requires 0 <= i < |xs|
  ensures Sum(xs[..i+1]) == Sum(xs[..i]) + xs[i]
{
  if i == 0 {
    assert xs[..1] == [xs[0]];
    assert Sum(xs[..1]) == Sum([xs[0]]) == xs[0];
    assert xs[..0] == [];
    assert Sum(xs[..0]) == 0;
  } else {
    assert xs[..i+1] == xs[..i] + [xs[i]];
    // The Sum function definition handles this case
  }
}

//IMPL
method SumArray(xs: array<int>) returns (s: int)
  ensures s == Sum(xs[..])
{
  s := 0;
  var i := 0;
  while i < xs.Length
    invariant 0 <= i <= xs.Length
    invariant s == Sum(xs[..i])
  {
    /* code modified by LLM (iteration 4): Simplified lemma application by directly calling on array sequence slice */
    SumProperty(xs[..], i);
    assert Sum(xs[..i+1]) == Sum(xs[..i]) + xs[..][i];
    assert xs[..][i] == xs[i];
    
    s := s + xs[i];
    i := i + 1;
  }
}