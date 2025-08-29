// <vc-helpers>
// </vc-helpers>

// <vc-description>
/*
function_signature: def eat(number: Nat, need: Nat, remaining: Nat) -> List Nat
You're a hungry rabbit, and you already have eaten a certain number of carrots, but now you need to eat more carrots to complete the day's meals. you should return an array of [ total number of eaten carrots after your meals, the number of carrots left after your meals ] if there are not enough remaining carrots, you will eat all remaining carrots, but will still be hungry.
*/
// </vc-description>

// <vc-spec>
method eat(number: nat, need: nat, remaining: nat) returns (result: seq<nat>)
  ensures |result| == 2
  ensures result[0] == number + (if remaining >= need then need else remaining)
  ensures result[1] == (if remaining >= need then remaining - need else 0)
// </vc-spec>
// <vc-code>
{
  if remaining >= need {
    result := [number + need, remaining - need];
  } else {
    result := [number + remaining, 0];
  }
}
// </vc-code>
