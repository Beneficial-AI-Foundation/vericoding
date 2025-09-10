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
lemma MaxLemma(a: int, b: int, c: int)
  ensures a >= b && a >= c ==> a >= b && a >= c
  ensures b >= a && b >= c ==> b >= a && b >= c
  ensures c >= a && c >= b ==> c >= a && c >= b
{
}

lemma ZeroFlipsLemma(sequence: seq<int>, start: int, end: int, K: int)
  requires 0 <= start <= end <= |sequence|
  requires K == 0
  ensures forall i :: start <= i < end ==> sequence[i] == 1
{
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
  result := 0;
  var left := 0;
  var current := 0;
  var flipsUsed := 0;
  
  for right := 0 to N
    invariant 0 <= left <= right <= N
    invariant flipsUsed <= K
    invariant current == right - left
    invariant result >= 0
    invariant result <= N
  {
    if right < N && bits[right] == 0 {
      flipsUsed := flipsUsed + 1;
    }
    
    while flipsUsed > K && left <= right {
      if left < N && bits[left] == 0 {
        flipsUsed := flipsUsed - 1;
      }
      left := left + 1;
    }
    
    current := right - left + 1;
    if current > result {
      result := current;
    }
  }
}
// </vc-code>

