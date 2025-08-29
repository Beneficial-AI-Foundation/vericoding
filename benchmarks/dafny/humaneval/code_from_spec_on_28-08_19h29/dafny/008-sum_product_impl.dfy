function sum(s: seq<int>) : int {
    if |s| == 0 then 0 else s[0] + sum(s[1..])
}
function prod(s: seq<int>) : int {
    if |s| == 0 then 1 else s[0] * prod(s[1..])
}

// <vc-helpers>
// No additional helpers needed beyond the provided sum and prod functions
// </vc-helpers>

// <vc-description>
/*
function_signature: def sum_product(numbers: List[int]) -> Tuple[int, int]
For a given list of integers, return a tuple consisting of a sum and a product of all the integers in a list. Empty sum should be equal to 0 and empty product should be equal to 1.
*/
// </vc-description>

// <vc-spec>
method SumProduct(numbers: seq<int>) returns (sumResult: int, prodResult: int)
  ensures sumResult == sum(numbers)
  ensures prodResult == prod(numbers)
// </vc-spec>
// <vc-code>
{
  sumResult := sum(numbers);
  prodResult := prod(numbers);
}
// </vc-code>
