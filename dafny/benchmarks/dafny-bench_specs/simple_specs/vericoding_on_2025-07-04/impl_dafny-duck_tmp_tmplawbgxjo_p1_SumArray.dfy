//ATOM
// Given an array of integers, it returns the sum. [1,3,3,2]->9

function Sum(xs: seq<int>): int {
  if |xs| == 0 then 0 else Sum(xs[..|xs|-1]) + xs[|xs|-1]
}

/* code modified by LLM (iteration 1): Added helper lemma to prove the relationship between Sum of consecutive slices */
lemma SumAppendLemma(xs: seq<int>, i: int)
  requires 0 <= i < |xs|
  ensures Sum(xs[..i+1]) == Sum(xs[..i]) + xs[i]
{
  if i == 0 {
    assert xs[..1] == [xs[0]];
    assert xs[..0] == [];
    assert Sum(xs[..0]) == 0;
    assert Sum(xs[..1]) == Sum([xs[0]]) == xs[0];
  } else {
    var prefix := xs[..i+1];
    assert prefix == xs[..i] + [xs[i]];
    assert |prefix| == i + 1;
    assert prefix[|prefix|-1] == xs[i];
    assert prefix[..|prefix|-1] == xs[..i];
    assert Sum(prefix) == Sum(prefix[..|prefix|-1]) + prefix[|prefix|-1];
    assert Sum(xs[..i+1]) == Sum(xs[..i]) + xs[i];
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
    /* code modified by LLM (iteration 2): Apply lemma before updating s, then update s and i together to maintain invariant */
    SumAppendLemma(xs[..], i);
    s := s + xs[i];
    i := i + 1;
  }
}