// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
function EatResult(number: int, need: int, remaining: int): seq<int>
  requires number >= 0 && need >= 0 && remaining >= 0
{
  if remaining >= need then [number + need, remaining - need] else [number + remaining, 0]
}
// </vc-helpers>

// <vc-spec>
method eat(number : int, need : int, remaining : int) returns (result: seq<int>)

  requires number >= 0 && need >= 0 && remaining >= 0

  ensures |result| == 2
  ensures remaining >= need ==> result[0] == number + need && result[1] == remaining - need
  ensures remaining < need ==> result[0] == number + remaining && result[1] == 0
// </vc-spec>
// <vc-code>
{
  result := EatResult(number, need, remaining);
}
// </vc-code>
