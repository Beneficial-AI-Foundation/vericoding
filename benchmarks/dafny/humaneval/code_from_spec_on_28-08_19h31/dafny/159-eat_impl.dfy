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
  var eaten := 0;
  var left := remaining;
  
  if remaining >= need {
    eaten := number + need;
    left := remaining - need;
  } else {
    eaten := number + remaining;
    left := 0;
  }
  
  result := [eaten, left];
}
// </vc-code>
