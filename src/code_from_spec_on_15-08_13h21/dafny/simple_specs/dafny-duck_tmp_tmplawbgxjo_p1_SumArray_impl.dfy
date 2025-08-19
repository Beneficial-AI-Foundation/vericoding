function Sum(xs: seq<int>): int {
  if |xs| == 0 then 0 else Sum(xs[..|xs|-1]) + xs[|xs|-1]
}

//IMPL SPEC
method SumArray(xs: array<int>) returns (s: int)
  ensures s == Sum(xs[..])
{
  s := 0;
  var i := 0;
  while i < xs.Length
    invariant 0 <= i <= xs.Length
    invariant s == Sum(xs[..i])
  {
    /* code modified by LLM (iteration 1): added assertion to help Dafny prove that Sum(xs[..i+1]) == Sum(xs[..i]) + xs[i] */
    assert xs[..i+1] == xs[..i] + [xs[i]];
    s := s + xs[i];
    i := i + 1;
  }
  /* code modified by LLM (iteration 1): added assertion to prove that xs[..i] == xs[..] when i == xs.Length */
  assert i == xs.Length;
  assert xs[..i] == xs[..];
}