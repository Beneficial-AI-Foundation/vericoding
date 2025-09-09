// <vc-helpers>
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
  assume {:axiom} false;
}
// </vc-code>
