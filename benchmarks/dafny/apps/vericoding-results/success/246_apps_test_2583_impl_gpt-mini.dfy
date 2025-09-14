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
function isLimitedPrimeHelper(p: int, k: int): bool
  requires p >= 1
  requires k >= 3
  decreases p - k
{
  if k * k > p then true
  else if p % k == 0 then false
  else isLimitedPrimeHelper(p, k + 2)
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
  var n := input[0];
  var arr := new string[n];
  var i := 1;
  while i < |input|
    invariant 1 <= i <= |input|
    invariant arr.Length == input[0]
    invariant forall j :: 1 <= j < i ==> arr[j-1] == determineWinner(input[j])
    invariant forall k :: 0 <= k < i-1 ==> arr[k] == "FastestFinger" || arr[k] == "Ashishgup"
  {
    arr[i-1] := determineWinner(input[i]);
    assert arr[i-1] == "FastestFinger" || arr[i-1] == "Ashishgup";
    i := i + 1;
  }
  result := arr[..];
}
// </vc-code>

