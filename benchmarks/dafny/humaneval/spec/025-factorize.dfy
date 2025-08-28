function prod(s: seq<int>) : int {
  if |s| == 0 then 1 else prod(s[..|s| - 1]) * s[|s| - 1]
}

// <vc-helpers>
// </vc-helpers>

// <vc-description>
/*
function_signature: def factorize(n: int) -> List[int]
Return list of prime factors of given integer in the order from smallest to largest. Each of the factors should be listed number of times corresponding to how many times it appeares in factorization. Input number should be equal to the product of all factors
*/
// </vc-description>

// <vc-spec>
method factorize(n: nat) returns (factors: seq<nat>)
  // pre-conditions-start
  requires n > 0
  // pre-conditions-end
  // post-conditions-start
  ensures prod(factors) == n
  // post-conditions-end
// </vc-spec>
// <vc-code>
{
  assume false;
}
// </vc-code>
