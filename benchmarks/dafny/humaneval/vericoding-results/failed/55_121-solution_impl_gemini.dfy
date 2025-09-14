// <vc-preamble>
function sum(s: seq<int>, p: seq<bool>) : int
  requires |s| == |p|
{
  if |s| == 0 then 0 else (if p[0] then s[0] else 0) + sum(s[1..], p[1..])
}
// </vc-preamble>

// <vc-helpers>
lemma SumPrefix(s: seq<int>, p: seq<bool>)
  requires |s| > 0 && |s| == |p|
  ensures sum(s, p) == sum(s[..|s|-1], p[..|s|-1]) + (if p[|s|-1] then s[|s|-1] else 0)
  decreases |s|
{
  if |s| > 1 {
    SumPrefix(s[1..], p[1..]);
  }
}
// </vc-helpers>

// <vc-spec>
method solution(numbers: seq<int>) returns (s: int)

  ensures s == sum(numbers, seq(|numbers|, i requires 0 <= i < |numbers| => i % 2 == 0 && numbers[i] % 2 == 1))
// </vc-spec>
// <vc-code>
{
  s := 0;
  var i := 0;
  while i < |numbers|
    invariant 0 <= i <= |numbers|
    invariant s == sum(numbers[..i], seq(i, j requires 0 <= j < i => j % 2 == 0 && numbers[j] % 2 == 1))
  {
    if i % 2 == 0 && numbers[i] % 2 == 1 {
      s := s + numbers[i];
    }
    i := i + 1;
  }
}
// </vc-code>
