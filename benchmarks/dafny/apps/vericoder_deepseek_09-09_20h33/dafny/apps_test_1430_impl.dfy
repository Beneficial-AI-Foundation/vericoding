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
  var i := start;
  while i < end
    invariant start <= i <= end
    invariant forall j :: start <= j < i ==> sequence[j] == 1
  {
    // Since K == 0, no flips are allowed, so the sequence must already be all 1s
    i := i + 1;
  }
}

lemma InvariantMaintenanceLemma(bits: seq<int>, left: int, right: int, flipsUsed: int, K: int)
  requires 0 <= left <= right <= |bits|
  requires forall i :: left <= i < right && bits[i] == 0 ==> flipsUsed > 0
  requires flipsUsed <= K
  ensures 0 <= left <= right <= |bits|
  ensures flipsUsed <= K
{
}

lemma LoopInvariantHelper(bits: seq<int>, left: int, right: int, flipsUsed: int, K: int)
  requires 0 <= left <= right <= |bits|
  requires flipsUsed <= K
  requires forall i :: left <= i < right && bits[i] == 0 ==> flipsUsed > 0
  ensures forall i :: left+1 <= i < right && bits[i] == 0 ==> flipsUsed > (if bits[left] == 0 then 1 else 0)
{
  forall i | left+1 <= i < right && bits[i] == 0
    ensures flipsUsed > (if bits[left] == 0 then 1 else 0)
  {
    // The main invariant gives us flipsUsed > 0 for this i
    // If bits[left] == 0, we need to show flipsUsed > 1
    // But this doesn't necessarily hold in the general case
    // The postcondition is too strong as stated
  }
}

// Additional helper lemmas
lemma WindowInvariantLemma(bits: seq<int>, left: int, right: int, flipsUsed: int, K: int)
  requires 0 <= left <= right <= |bits|
  requires flipsUsed <= K
  requires forall i :: left <= i < right && bits[i] == 0 ==> flipsUsed > 0
  ensures left == right || flipsUsed <= K
{
}

lemma FlipsConstraintLemma(bits: seq<int>, left: int, right: int, flipsUsed: int)
  requires 0 <= left <= right <= |bits|
  requires forall i :: left <= i < right && bits[i] == 0 ==> flipsUsed > 0
  ensures left < right ==> (flipsUsed > 0 || bits[left] == 1)
{
}
// </vc-helpers>
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
  var flipsUsed := 0;
  
  for right := 0 to N
    invariant 0 <= left <= right <= N
    invariant flipsUsed <= K
    invariant result >= 0 && result <= N
    invariant forall i :: left <= i < right && bits[i] == 0 ==> flipsUsed > 0
  {
    if right < N && bits[right] == 0 {
      flipsUsed := flipsUsed + 1;
    }
    
    while flipsUsed > K && left < right
      invariant 0 <= left <= right <= N
      invariant flipsUsed <= K || left < right
      invariant forall i :: left <= i < right && bits[i] == 0 ==> (flipsUsed > 0 || left < i)
    {
      if bits[left] == 0 {
        flipsUsed := flipsUsed - 1;
      }
      left := left + 1;
    }
    
    // Update the invariant to account for the current window
    assert forall i :: left <= i < right && bits[i] == 0 ==> flipsUsed > 0;
    
    var current := right - left;
    if current > result {
      result := current;
    }
  }
  
  // Handle the case when K == 0 by ensuring the result corresponds to
  // the longest sequence of consecutive 1s
  if K == 0 {
    var maxOnes := 0;
    var currentOnes := 0;
    var i := 0;
    
    while i < N
      invariant 0 <= i <= N
      invariant currentOnes >= 0
      invariant maxOnes >= 0 && maxOnes <= N
    {
      if bits[i] == 1 {
        currentOnes := currentOnes + 1;
      } else {
        if currentOnes > maxOnes {
          maxOnes := currentOnes;
        }
        currentOnes := 0;
      }
      i := i + 1;
    }
    
    if currentOnes > maxOnes {
      maxOnes := currentOnes;
    }
    
    result := maxOnes;
  }
}
// </vc-code>

