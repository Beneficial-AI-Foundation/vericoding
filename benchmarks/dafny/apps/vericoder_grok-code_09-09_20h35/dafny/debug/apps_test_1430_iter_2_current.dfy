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
  while start <= N {
    var count := 0;
    var end := start;
    while end <= N {
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

