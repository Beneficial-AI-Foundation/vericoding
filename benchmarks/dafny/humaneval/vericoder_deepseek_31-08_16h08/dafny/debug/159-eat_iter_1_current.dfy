

// <vc-helpers>
lemma RemainderLemma(a: int, b: int)
  requires a >= 0 && b >= 0
  ensures a >= b ==> a - b >= 0
  ensures a < b ==> 0 >= 0
{
}
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
  var new_remaining := 0;
  
  if remaining >= need {
    eaten := need;
    new_remaining := remaining - need;
  } else {
    eaten := remaining;
    new_remaining := 0;
  }
  
  RemainderLemma(remaining, need);
  result := [number + eaten, new_remaining];
}
// </vc-code>

