predicate ValidInput(n: int, arr: seq<int>)
{
  n >= 1 && |arr| == n
}

function sum_seq(s: seq<int>): int
{
  if |s| == 0 then 0
  else s[0] + sum_seq(s[1..])
}

predicate CorrectResult(n: int, arr: seq<int>, result: int)
  requires ValidInput(n, arr)
{
  (sum_seq(arr) % n == 0 ==> result == n) &&
  (sum_seq(arr) % n != 0 ==> result == n - 1) &&
  (result == n || result == n - 1)
}

// <vc-helpers>
function sum_seq_iter(arr: seq<int>, i: int): int
  requires 0 <= i <= |arr|
  ensures sum_seq_iter(arr, i) == sum_seq(arr[i..])
{
  if i == |arr| then
    0
  else
    arr[i] + sum_seq_iter(arr, i + 1)
}

lemma SumSeqIterIsSumSeq(arr: seq<int>)
  ensures sum_seq_iter(arr, 0) == sum_seq(arr)
{
  // The ensures clause is already proved by the function definition itself.
  // No explicit proof steps are needed here.
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, arr: seq<int>) returns (result: int)
  requires ValidInput(n, arr)
  ensures CorrectResult(n, arr, result)
// </vc-spec>
// <vc-code>
{
  var s := 0;
  var i := 0;
  SumSeqIterIsSumSeq(arr); // Ensure sum_seq_iter(arr, 0) == sum_seq(arr)
  while i < n
    invariant 0 <= i <= n
    invariant s == sum_seq(arr[..i])
  {
    s := s + arr[i];
    i := i + 1;
  }

  // After the loop, s == sum_seq(arr[..n]) which is sum_seq(arr)
  assert s == sum_seq(arr);

  if s % n == 0 {
    result := n;
  } else {
    result := n - 1;
  }
}
// </vc-code>

