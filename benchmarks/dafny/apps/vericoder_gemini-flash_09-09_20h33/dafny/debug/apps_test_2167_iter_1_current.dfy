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
function method sum_seq_iter(arr: seq<int>, i: int): int
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
  // Base case: sum_seq_iter(arr, |arr|) == 0 and sum_seq(arr[|arr|..]) == sum_seq([]) == 0
  // Inductive step: assuming sum_seq_iter(arr, i+1) == sum_seq(arr[i+1..])
  // We need to show sum_seq_iter(arr, i) == sum_seq(arr[i..])
  // sum_seq_iter(arr, i) = arr[i] + sum_seq_iter(arr, i+1) (by definition)
  //                    = arr[i] + sum_seq(arr[i+1..]) (by induction hypothesis)
  //                    = sum_seq(arr[i..]) (by definition of sum_seq)
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
  while i < n
    invariant 0 <= i <= n
    invariant s == sum_seq_iter(arr, 0) - sum_seq_iter(arr, i)
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

