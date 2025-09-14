// <vc-preamble>
function sum(s: seq<int>) : int {
    if |s| == 0 then 0 else s[0] + sum(s[1..])
}
function prod(s: seq<int>) : int {
    if |s| == 0 then 1 else s[0] * prod(s[1..])
}
// </vc-preamble>

// <vc-helpers>
lemma lemma_sum_append(s: seq<int>, x: int)
  ensures sum(s + [x]) == sum(s) + x
{
  if |s| == 0 {
  } else {
    lemma_sum_append(s[1..], x);
  }
}

lemma lemma_prod_append(s: seq<int>, x: int)
  ensures prod(s + [x]) == prod(s) * x
{
  if |s| == 0 {
  } else {
    lemma_prod_append(s[1..], x);
  }
}
// </vc-helpers>

// <vc-spec>
method sum_product(numbers: seq<int>) returns (s : int, p : int)

    ensures s == sum(numbers)
    ensures p == prod(numbers)
// </vc-spec>
// <vc-code>
{
  s := 0;
  p := 1;
  var i: nat := 0;
  while i < |numbers|
    invariant i <= |numbers|
    invariant s == sum(numbers[0..i])
    invariant p == prod(numbers[0..i])
  {
    s := s + numbers[i];
    p := p * numbers[i];
    i := i + 1;
  }
}
// </vc-code>
