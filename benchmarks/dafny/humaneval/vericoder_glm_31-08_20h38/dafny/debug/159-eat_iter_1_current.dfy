

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method eat(number : int, need : int, remaining : int) returns (result: seq<int>)
  // pre-conditions-start
  requires number >= 0 && need >= 0 && remaining >= 0
  // pre-conditions-end
  // post-conditions-start
  ensures |result| == 2
  ensures remaining >= need ==> result[0] == number + need && result[1] == remaining - need
  ensures remaining < need ==> result[0] == number + remaining && result[1] == 0
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  if remaining >= need then
    return [number + need, remaining - need];
  else
    return [number + remaining, 0];
}
// </vc-code>

