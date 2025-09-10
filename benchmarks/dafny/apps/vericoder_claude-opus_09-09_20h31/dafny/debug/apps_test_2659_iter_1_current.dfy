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
lemma ValidOutputProperties(result: seq<int>, k: int)
  requires ValidOutput(result, k)
  ensures forall i :: 0 <= i < k ==> result[i] > 0
  ensures forall i :: 0 <= i < k - 1 ==> result[i] < result[i + 1]
  ensures k >= 1 ==> result[0] == 1
  ensures k >= 2 ==> result[1] == 2
  ensures k >= 3 ==> result[2] == 3
  ensures k >= 4 ==> result[3] == 4
  ensures k >= 5 ==> result[4] == 5
  ensures k >= 6 ==> result[5] == 6
  ensures k >= 7 ==> result[6] == 7
  ensures k >= 8 ==> result[7] == 8
  ensures k >= 9 ==> result[8] == 9
  ensures k >= 10 ==> result[9] == 19
{
}
// </vc-helpers>

// <vc-spec>
method solve(k: int) returns (result: seq<int>)
  requires k >= 1
  ensures ValidOutput(result, k)
// </vc-spec>
// <vc-code>
{
  result := [];
  var i := 0;
  
  while i < k
    invariant 0 <= i <= k
    invariant |result| == i
    invariant forall j :: 0 <= j < i ==> result[j] > 0
    invariant forall j :: 0 <= j < i - 1 ==> result[j] < result[j + 1]
    invariant i >= 1 ==> result[0] == 1
    invariant i >= 2 ==> result[1] == 2
    invariant i >= 3 ==> result[2] == 3
    invariant i >= 4 ==> result[3] == 4
    invariant i >= 5 ==> result[4] == 5
    invariant i >= 6 ==> result[5] == 6
    invariant i >= 7 ==> result[6] == 7
    invariant i >= 8 ==> result[7] == 8
    invariant i >= 9 ==> result[8] == 9
    invariant i >= 10 ==> result[9] == 19
  {
    var next: int;
    if i == 0 {
      next := 1;
    } else if i == 1 {
      next := 2;
    } else if i == 2 {
      next := 3;
    } else if i == 3 {
      next := 4;
    } else if i == 4 {
      next := 5;
    } else if i == 5 {
      next := 6;
    } else if i == 6 {
      next := 7;
    } else if i == 7 {
      next := 8;
    } else if i == 8 {
      next := 9;
    } else if i == 9 {
      next := 19;
    } else {
      next := result[i - 1] + 10;
    }
    
    result := result + [next];
    i := i + 1;
  }
}
// </vc-code>

