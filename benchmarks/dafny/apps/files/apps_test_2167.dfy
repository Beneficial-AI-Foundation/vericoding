Given an array of n integers, find the maximum number of elements that can be made equal
after performing any number of operations where each operation chooses two different elements
and simultaneously increases one by 1 and decreases the other by 1.

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

lemma sum_seq_append(s: seq<int>, x: int)
  ensures sum_seq(s + [x]) == sum_seq(s) + x
{
  if |s| == 0 {
    assert s + [x] == [x];
    assert sum_seq([x]) == x + sum_seq([]);
    assert sum_seq([]) == 0;
  } else {
    assert (s + [x])[0] == s[0];
    assert (s + [x])[1..] == s[1..] + [x];
    sum_seq_append(s[1..], x);
  }
}

method solve(n: int, arr: seq<int>) returns (result: int)
  requires ValidInput(n, arr)
  ensures CorrectResult(n, arr, result)
{
  var sum := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant sum == sum_seq(arr[..i])
  {
    sum := sum + arr[i];
    i := i + 1;
    sum_seq_append(arr[..i-1], arr[i-1]);
    assert arr[..i-1] + [arr[i-1]] == arr[..i];
    assert sum == sum_seq(arr[..i]);
  }

  assert i == n;
  assert arr[..n] == arr;
  assert sum == sum_seq(arr);

  if sum % n == 0 {
    result := n;
  } else {
    result := n - 1;
  }
}
