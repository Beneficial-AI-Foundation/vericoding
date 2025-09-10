predicate ValidInput(N: int, K: int, S: string)
{
    N > 0 && K >= 0 && |S| == N && 
    forall i :: 0 <= i < |S| ==> S[i] == '0' || S[i] == '1'
}

function StringToBits(S: string): seq<int>
    requires forall i :: 0 <= i < |S| ==> S[i] == '0' || S[i] == '1'
{
    seq(|S|, i requires 0 <= i < |S| => if S[i] == '0' then 0 else 1)
}

predicate ValidResult(result: int, N: int)
{
    0 <= result <= N
}

// <vc-helpers>
function NoOfZeros(s: seq<int>, lo: int, hi: int): int
  requires 0 <= lo <= hi <= |s|
  decreases hi - lo
{
  if lo == hi then 0 else if s[lo] == 0 then 1 + NoOfZeros(s, lo+1, hi) else NoOfZeros(s, lo+1, hi)
}
// </vc-helpers>

// <vc-spec>
method solve(N: int, K: int, S: string) returns (result: int)
    requires ValidInput(N, K, S)
    ensures ValidResult(result, N)
// </vc-spec>
// <vc-code>
{
  var bits := StringToBits(S);
  var maxL := 0;
  var start := 0;
  while start <= N
    invariant 0 <= start <= N+1;
    invariant maxL <= N;
    invariant forall i :: 0 <= i < start ==> forall j :: i <= j <= N ==> (NoOfZeros(bits, i, j) <= K) implies j - i <= maxL;
  {
    var count := 0;
    var end := start;
    while end <= N
      invariant start <= end <= N;
      invariant count == NoOfZeros(bits, start, end);
    {
      if end < N && bits[end] == 0 {
        count := count + 1;
      }
      if count <= K {
        var current_len := if end < N then end - start + 1 else N - start;
        if current_len > maxL {
          maxL := current_len;
        }
      }
      end := end + 1;
    }
    start := start + 1;
  }
  result := maxL;
}
// </vc-code>

