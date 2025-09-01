

// <vc-helpers>
function sum(s: seq<int>, p: seq<bool>) : int
  requires |s| == |p|
{
  if |s| == 0 then 0 else (if p[0] then s[0] else 0) + sum(s[1..], p[1..])
}
// </vc-helpers>

// <vc-spec>
method solution(numbers: seq<int>) returns (s: int)
  // post-conditions-start
  ensures s == sum(numbers, seq(|numbers|, i requires 0 <= i < |numbers| => i % 2 == 0 && numbers[i] % 2 == 1))
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  var s := 0;
  var i := 0;
  while i < |numbers|
    invariant 0 <= i <= |numbers|
    invariant s == sum(numbers[0..<i], seq(i, k requires 0 <= k < i => k % 2 == 0 && numbers[k] % 2 == 1))
  {
    if i % 2 == 0 && numbers[i] % 2 == 1 {
      s := s + numbers[i];
    }
    i := i + 1;
  }
  return s;
}
// </vc-code>

function sum(s: seq<int>, p: seq<bool>) : int
  requires |s| == |p|
{
  if |s| == 0 then 0 else (if p[0] then s[0] else 0) + sum(s[1..], p[1..])
}
// pure-end