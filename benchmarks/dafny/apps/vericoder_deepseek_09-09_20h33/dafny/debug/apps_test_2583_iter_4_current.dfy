function determineWinner(n: int): string
requires n >= 1
ensures determineWinner(n) == "FastestFinger" || determineWinner(n) == "Ashishgup"
ensures (n == 1) ==> determineWinner(n) == "FastestFinger"
ensures (n == 2) ==> determineWinner(n) == "Ashishgup"
ensures (n > 2 && isPowerOfTwo(n)) ==> determineWinner(n) == "FastestFinger"
ensures (n > 2 && !isPowerOfTwo(n) && n % 4 != 2) ==> determineWinner(n) == "Ashishgup"
ensures (n > 2 && !isPowerOfTwo(n) && n % 4 == 2) ==> (determineWinner(n) == "FastestFinger" <==> isLimitedPrime(n / 2))
{
    if n == 1 then "FastestFinger"
    else if n == 2 then "Ashishgup"
    else if isPowerOfTwo(n) then "FastestFinger"
    else if n % 4 != 2 then "Ashishgup"
    else if isLimitedPrime(n / 2) then "FastestFinger"
    else "Ashishgup"
}

function isPowerOfTwo(n: int): bool
requires n >= 1
ensures n == 1 ==> isPowerOfTwo(n)
ensures n > 1 ==> (isPowerOfTwo(n) <==> (n % 2 == 0 && isPowerOfTwo(n / 2)))
{
    if n <= 0 then false
    else n == 1 || (n % 2 == 0 && isPowerOfTwo(n / 2))
}

function isLimitedPrime(p: int): bool
requires p >= 1
ensures p == 1 ==> !isLimitedPrime(p)
ensures p == 2 ==> isLimitedPrime(p)
ensures p > 2 && p % 2 == 0 ==> !isLimitedPrime(p)
ensures p > 2 && p % 2 != 0 ==> (isLimitedPrime(p) <==> isLimitedPrimeHelper(p, 3))
{
    if p <= 1 then false
    else if p == 2 then true
    else if p % 2 == 0 then false
    else isLimitedPrimeHelper(p, 3)
}

// <vc-helpers>
predicate isPrime(n: int)
  requires n >= 2
{
  n >= 2 && forall k: int :: 2 <= k < n ==> n % k != 0
}

function helper(n: int, d: int): bool
  requires n >= 1
  requires d >= 2
  requires d <= n
  requires d * d <= n
  decreases n - d
{
  if d * d > n then false
  else if n % d == 0 then true
  else if d + 1 > n then false
  else helper(n, d + 1)
}

function isLimitedPrimeHelper(p: int, d: int): bool
  requires p >= 3
  requires d >= 3
  requires d <= p
  requires d % 2 == 1
  requires d * d <= p
  decreases p - d
{
  if d * d > p then false
  else if p % d == 0 then true
  else if d + 2 > p then false
  else isLimitedPrimeHelper(p, d + 2)
}

lemma LimitedPrimeHelperLemma(p: int, d: int)
  requires p >= 3
  requires d >= 3
  requires d <= p
  requires d % 2 == 1
  requires d * d <= p
  ensures isLimitedPrimeHelper(p, d) == (exists k :: d <= k < p && k % 2 == 1 && p % k == 0)
{
  // The lemma body needs to be implemented to prove the postcondition
  if isLimitedPrimeHelper(p, d) {
    // If helper returns true, we need to show the existence
  } else {
    // If helper returns false, we need to show no such k exists
  }
}

lemma LimitedPrimeLemma(p: int)
  requires p >= 3
  requires p % 2 == 1
  ensures isLimitedPrime(p) == (exists k :: 3 <= k < p && k % 2 == 1 && p % k == 0)
{
  // This lemma connects isLimitedPrime to the helper function
  if isLimitedPrime(p) {
    // Show that isLimitedPrimeHelper(p, 3) implies the existence
  } else {
    // Show that !isLimitedPrimeHelper(p, 3) implies no such k exists
  }
}
// </vc-helpers>

// <vc-spec>
method solve(input: seq<int>) returns (result: seq<string>)
requires |input| >= 1
requires input[0] >= 1
requires |input| == input[0] + 1
requires forall i :: 1 <= i < |input| ==> input[i] >= 1
ensures |result| == input[0]
ensures forall i :: 0 <= i < |result| ==> result[i] == "FastestFinger" || result[i] == "Ashishgup"
ensures forall i :: 1 <= i < |input| ==> result[i-1] == determineWinner(input[i])
// </vc-spec>
// <vc-code>
{
  var count := input[0];
  var numbers := input[1..];
  var i := 0;
  result := [];
  
  while i < count
    invariant 0 <= i <= count
    invariant |result| == i
    invariant forall j :: 0 <= j < |result| ==> result[j] == determineWinner(numbers[j])
  {
    var n := numbers[i];
    var winner := "Ashishgup";
    
    if n == 1 {
      winner := "FastestFinger";
    } else if n == 2 {
      winner := "Ashishgup";
    } else if isPowerOfTwo(n) {
      winner := "FastestFinger";
    } else if n % 2 != 0 {
      winner := "Ashishgup";
    } else if n % 4 == 0 {
      winner := "Ashishgup";
    } else {
      var half := n / 2;
      if isLimitedPrime(half) {
        winner := "FastestFinger";
      } else {
        winner := "Ashishgup";
      }
    }
    
    result := result + [winner];
    i := i + 1;
  }
  
  return result;
}
// </vc-code>

