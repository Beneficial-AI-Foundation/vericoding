// <vc-preamble>
function sum(s: seq<int>, p: seq<bool>) : int
  requires |s| == |p|
{
  if |s| == 0 then 0 else (if p[0] then s[0] else 0) + sum(s[1..], p[1..])
}
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method solution(numbers: seq<int>) returns (s: int)

  ensures s == sum(numbers, seq(|numbers|, i requires 0 <= i < |numbers| => i % 2 == 0 && numbers[i] % 2 == 1))
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): use sum function with predicate sequence */
{
  s := sum(numbers, seq(|numbers|, i requires 0 <= i < |numbers| => i % 2 == 0 && numbers[i] % 2 == 1));
}
// </vc-code>
