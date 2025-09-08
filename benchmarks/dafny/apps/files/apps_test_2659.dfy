Given S(n) as the sum of digits in decimal notation of integer n, an integer n is called a "Snuke number" 
if for all positive integers m > n, the inequality n/S(n) ≤ m/S(m) holds.
Given an integer K, find the K smallest Snuke numbers.

function SumOfDigits(n: int): int
  requires n >= 0
{
  if n < 10 then n
  else (n % 10) + SumOfDigits(n / 10)
}

predicate ValidOutput(result: seq<int>, k: int)
{
  |result| == k &&
  (forall i :: 0 <= i < k ==> result[i] > 0) &&
  (forall i :: 0 <= i < k - 1 ==> result[i] < result[i + 1]) &&
  (k >= 1 ==> result[0] == 1) &&
  (k >= 2 ==> result[1] == 2) &&
  (k >= 3 ==> result[2] == 3) &&
  (k >= 4 ==> result[3] == 4) &&
  (k >= 5 ==> result[4] == 5) &&
  (k >= 6 ==> result[5] == 6) &&
  (k >= 7 ==> result[6] == 7) &&
  (k >= 8 ==> result[7] == 8) &&
  (k >= 9 ==> result[8] == 9) &&
  (k >= 10 ==> result[9] == 19)
}

method solve(k: int) returns (result: seq<int>)
  requires k >= 1
  ensures ValidOutput(result, k)
{
  var a := 0;
  var b := 1;
  var output := [];
  var i := 0;

  while i < k
    invariant 0 <= i <= k
    invariant |output| == i
    invariant a >= 0
    invariant b >= 1
    invariant forall j :: 0 <= j < i ==> output[j] > 0
    invariant i == 0 ==> a == 0 && b == 1
    invariant i == 1 ==> a == 1 && b == 1
    invariant i == 2 ==> a == 2 && b == 1
    invariant i == 3 ==> a == 3 && b == 1
    invariant i == 4 ==> a == 4 && b == 1
    invariant i == 5 ==> a == 5 && b == 1
    invariant i == 6 ==> a == 6 && b == 1
    invariant i == 7 ==> a == 7 && b == 1
    invariant i == 8 ==> a == 8 && b == 1
    invariant i == 9 ==> a == 9 && b == 10
    invariant i >= 10 ==> a >= 19 && b >= 10
    invariant i >= 1 ==> output[0] == 1
    invariant i >= 2 ==> output[1] == 2  
    invariant i >= 3 ==> output[2] == 3
    invariant i >= 4 ==> output[3] == 4
    invariant i >= 5 ==> output[4] == 5
    invariant i >= 6 ==> output[5] == 6
    invariant i >= 7 ==> output[6] == 7
    invariant i >= 8 ==> output[7] == 8
    invariant i >= 9 ==> output[8] == 9
    invariant i >= 10 ==> output[9] == 19
    invariant i > 0 ==> output[i-1] == a
    invariant forall j :: 0 <= j < i - 1 ==> output[j] < output[j + 1]
  {
    a := a + b;
    output := output + [a];
    if b * SumOfDigits(a + b) < a + b {
      b := b * 10;
    }
    i := i + 1;
  }

  return output;
}
