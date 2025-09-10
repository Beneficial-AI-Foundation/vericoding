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
lemma SumSeqConcat(s: seq<int>, t: seq<int>)
  ensures sum_seq(s + t) == sum_seq(s) + sum_seq(t)
{
  if |s| == 0 {
    assert s + t == t;
    assert sum_seq(s + t) == sum_seq(t);
    assert sum_seq(s) == 0;
    assert 0 + sum_seq(t) == sum_seq(t);
  } else {
    SumSeqConcat(s[1..], t);
    assert sum_seq(s[1..] + t) == sum_seq(s[1..]) + sum_seq(t);
    assert sum_seq(s + t) == s[0] + sum_seq(s[1..] + t);
    assert s[0] + (sum_seq(s[1..]) + sum_seq(t)) == s[0] + sum_seq(s[1..]) + sum_seq(t);
    assert s[0] + sum_seq(s[1..]) == sum_seq(s);
  }
}
// </vc-helpers>

// <vc-spec>
method solve(n: int, arr: seq<int>) returns (result: int)
  requires ValidInput(n, arr)
  ensures CorrectResult(n, arr, result)
// </vc-spec>
// <vc-code>
{
  var sum := 0;
  for i := 0 to n-1
    invariant sum == sum_seq(arr[..i])
  {
    SumSeqConcat(arr[..i], [arr[i]]);
    calc {
      sum;
      == sum_seq(arr[..i]) + arr[i];
      {
        SumSeqConcat(arr[..i], [arr[i]]);
      }
      == sum_seq(arr[..i+1]);
    }
    sum := sum + arr[i];
  }
  assert sum == sum_seq(arr);
  if sum % n == 0 {
    result := n;
  } else {
    result := n - 1;
  }
}
// </vc-code>

