// Given an array of integers, it returns the sum. [1,3,3,2]->9

function Sum(xs: seq<int>): int {
    if |xs| == 0 then 0 else Sum(xs[..|xs|-1]) + xs[|xs|-1]
}

// <vc-helpers>
lemma Sum_snoc(xs: seq<int>, x: int)
  ensures Sum(xs + [x]) == Sum(xs) + x
{
  assert |xs + [x]| > 0;
  assert Sum(xs + [x]) == Sum((xs + [x])[..|xs + [x]| - 1]) + (xs + [x])[|xs + [x]| - 1];
  assert |xs + [x]| == |xs| + 1;
  assert (xs + [x])[..|xs + [x]| - 1] == (xs + [x])[..|xs|];
  assert (xs + [x])[..|xs|] == xs;
  assert (xs + [x])[|xs + [x]| - 1] == (xs + [x])[|xs|];
  assert (xs + [x])[|xs|] == x;
  assert Sum(xs + [x]) == Sum(xs) + x;
}

lemma Sum_TakeSnoc(s: seq<int>, i: int)
  requires 0 <= i < |s|
  ensures Sum(s[..i+1]) == Sum(s[..i]) + s[i]
{
  assert s[..i+1] == s[..i] + [s[i]];
  Sum_snoc(s[..i], s[i]);
  assert Sum(s[..i+1]) == Sum(s[..i]) + s[i];
}
// </vc-helpers>

// <vc-spec>
method SumArray(xs: array<int>) returns (s: int)
    ensures s == Sum(xs[..])
// </vc-spec>
// <vc-code>
{
  var i := 0;
  s := 0;
  assert Sum(xs[..0]) == 0;
  while i < xs.Length
    invariant 0 <= i <= xs.Length
    invariant s == Sum(xs[..i])
    decreases xs.Length - i
  {
    Sum_TakeSnoc(xs[..], i);
    assert (xs[..])[..i] == xs[..i];
    assert (xs[..])[..i+1] == xs[..i+1];
    assert (xs[..])[i] == xs[i];
    assert Sum(xs[..i+1]) == Sum(xs[..i]) + xs[i];
    s := s + xs[i];
    i := i + 1;
  }
  assert i == xs.Length;
  assert xs[..i] == xs[..];
  assert s == Sum(xs[..]);
}
// </vc-code>

