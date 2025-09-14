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

// <vc-helpers>
function {:compile} Range(a: int, b: int): seq<int>
  requires a <= b
  ensures |Range(a,b)| == b - a + 1
  ensures forall i :: 0 <= i < |Range(a,b)| ==> Range(a,b)[i] == a + i
  decreases b - a
{
  if a == b then [a] else [a] + Range(a+1, b)
}
// </vc-helpers>

// <vc-spec>
method solve(k: int) returns (result: seq<int>)
  requires k >= 1
  ensures ValidOutput(result, k)
// </vc-spec>
// <vc-code>
{
  if k <= 9 {
    result := Range(1, k);
  } else if k == 10 {
    result := [1, 2, 3, 4, 5, 6, 7, 8, 9, 19];
  } else {
    var head := [1, 2, 3, 4, 5, 6, 7, 8, 9, 19];
    var tail := Range(20, 20 + (k - 11));
    result := head + tail;
  }
}
// </vc-code>

