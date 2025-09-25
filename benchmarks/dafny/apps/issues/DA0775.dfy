// <vc-preamble>
function d(x: int, y: int): int
{
  if x - y > 1 || y - x > 1 then y - x else 0
}

function seq_sum(s: seq<int>): int
{
  if |s| == 0 then 0
  else s[0] + seq_sum(s[1..])
}

function sumPairs(line: seq<int>, n: int): int
  requires n >= 1
  requires |line| == n
{
  seq_sum(seq(n * n, k requires 0 <= k < n * n => 
    var i := k / n;
    var j := k % n;
    if i <= j then d(line[i], line[j]) else 0))
}

predicate ValidInput(n: int, line: seq<int>)
{
  n >= 1 &&
  |line| == n &&
  (forall i :: 0 <= i < n ==> line[i] >= 1) &&
  (forall i :: 0 <= i < n ==> line[i] <= 1000000000)
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int, line: seq<int>) returns (result: int)
  requires ValidInput(n, line)
  ensures result == sumPairs(line, n)
// </vc-spec>
// <vc-code>
{
  result := 0;
  
  for i := 0 to n
    invariant 0 <= i <= n
    invariant result == seq_sum(seq(i * n, k requires 0 <= k < i * n => 
      var ii := k / n;
      var jj := k % n;
      if ii <= jj then d(line[ii], line[jj]) else 0))
  {
    for j := i to n
      invariant i <= j <= n
      invariant result == seq_sum(seq(i * n, k requires 0 <= k < i * n => 
        var ii := k / n;
        var jj := k % n;
        if ii <= jj then d(line[ii], line[jj]) else 0)) +
        seq_sum(seq((j - i), k requires 0 <= k < (j - i) => d(line[i], line[i + k])))
    {
      result := result + d(line[i], line[j]);
    }
  }
}
// </vc-code>
