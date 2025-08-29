function prod(s: seq<int>) : int {
  if |s| == 0 then 1 else prod(s[..|s| - 1]) * s[|s| - 1]
}

// <vc-helpers>
predicate isPrime(n: int)
{
  n > 1 && forall k :: 2 <= k < n ==> n % k != 0
}

lemma PrimeFactorizationExists(n: int)
  requires n > 1
  ensures exists factors: seq<int> :: 
    (forall i :: 0 <= i < |factors| ==> isPrime(factors[i])) &&
    prod(factors) == n &&
    (forall i, j :: 0 <= i < j < |factors| ==> factors[i] <= factors[j])
{
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def factorize(n: int) -> List[int]
Return list of prime factors of given integer in the order from smallest to largest. Each of the factors should be listed number of times corresponding to how many times it appeares in factorization. Input number should be equal to the product of all factors
*/
// </vc-description>

// <vc-spec>
method factorize(n: int) returns (factors: seq<int>)
  requires n > 1
  ensures forall i :: 0 <= i < |factors| ==> isPrime(factors[i])
  ensures prod(factors) == n
  ensures forall i, j :: 0 <= i < j < |factors| ==> factors[i] <= factors[j]
// </vc-spec>
// <vc-code>
{
  var res: seq<int> := [];
  var num := n;
  var divisor := 2;
  
  while num > 1
    invariant num >= 1
    invariant prod(res) * num == n
    invariant forall i :: 0 <= i < |res| ==> isPrime(res[i])
    invariant forall i, j :: 0 <= i < j < |res| ==> res[i] <= res[j]
    invariant divisor >= 2
    invariant forall i :: 0 <= i < |res| ==> res[i] <= divisor
    decreases num
  {
    if num % divisor == 0 {
      res := res + [divisor];
      num := num / divisor;
    } else {
      divisor := divisor + 1;
      if divisor * divisor > num && num > 1 {
        res := res + [num];
        num := 1;
      }
    }
  }
  factors := res;
}
// </vc-code>
