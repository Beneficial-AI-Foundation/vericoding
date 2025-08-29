function tri(n: nat): nat
  decreases if n % 2 == 0 then 0 else n
{
  if n == 1 then 3
  else if n % 2 == 0 then 1 + n / 2
  else tri(n - 1) + tri(n - 2) + tri(n + 1)
}

// <vc-helpers>
function tri(n: nat): nat
  decreases if n % 2 == 0 then 0 else n
{
  if n == 1 then 3
  else if n % 2 == 0 then 1 + n / 2
  else tri(n - 1) + tri(n - 2) + tri(n + 1)
}
// </vc-helpers>

// <vc-description>
/*
function_signature: def tri(n: int) -> List[int]
Everyone knows Fibonacci sequence, it was studied deeply by mathematicians in the last couple centuries. However, what people don't know is Tribonacci sequence. Tribonacci sequence is defined by the recurrence: tri(1) = 3 tri(n) = 1 + n / 2, if n is even. tri(n) =  tri(n - 1) + tri(n - 2) + tri(n + 1), if n is odd. For example: tri(2) = 1 + (2 / 2) = 2 tri(4) = 3 tri(3) = tri(2) + tri(1) + tri(4) = 2 + 3 + 3 = 8 You are given a non-negative integer number n, you have to a return a list of the first n + 1 numbers of the Tribonacci sequence.
*/
// </vc-description>

// <vc-spec>
method ComputeTribonacci(n: nat) returns (seq: seq<nat>)
  ensures |seq| == n + 1
  ensures forall i :: 0 <= i < |seq| ==> seq[i] == tri(i)
// </vc-spec>
// <vc-code>
{
  var result: seq<nat> := [];
  var i := 0;
  while i < n + 1
    invariant 0 <= i <= n + 1
    invariant |result| == i
    invariant forall k :: 0 <= k < i ==> result[k] == tri(k)
  {
    result := result + [tri(i)];
    i := i + 1;
  }
  seq := result;
}
// </vc-code>
