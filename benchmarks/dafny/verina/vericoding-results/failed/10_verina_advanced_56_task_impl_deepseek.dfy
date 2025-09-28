// <vc-preamble>
/* Count how many times a specific value appears in the sequence */
function CountVal(val: int, xs: seq<int>): nat 
    decreases |xs|
{
    if |xs| == 0 then
        0
    else
        var rest := CountVal(val, xs[1..]);
        if xs[0] == val then rest + 1 else rest
}

/* Check whether one sequence is a subsequence of another (preserving relative order) */
predicate IsSubsequence(xs: seq<int>, ys: seq<int>) 
    decreases |xs| + |ys|
{
    if |xs| == 0 then
        true
    else if |ys| == 0 then
        false
    else
        if xs[0] == ys[0] then
            IsSubsequence(xs[1..], ys[1..])
        else
            IsSubsequence(xs, ys[1..])
}

function FilterNonZero(xs: seq<int>): seq<int>
{
    if |xs| == 0 then []
    else if xs[0] != 0 then [xs[0]] + FilterNonZero(xs[1..])
    else FilterNonZero(xs[1..])
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fix array access issues and termination */ 
function FindFirstZeroPosition(a: array<int>, start: int): (result: int)
  requires 0 <= start <= a.Length
  reads a
  decreases a.Length - start
  ensures start <= result <= a.Length
  ensures result == a.Length || a[result] == 0
  ensures forall i :: start <= i < result ==> a[i] != 0
{
  if start == a.Length then start
  else if a[start] == 0 then start
  else FindFirstZeroPosition(a, start + 1)
}

lemma NonZeroesPreserved(xs: seq<int>, result: seq<int>)
  requires |xs| > 0 && xs[0] != 0
  requires IsSubsequence(xs, result)
  ensures |result| > 0 && result[0] == xs[0]
{
}

function AllZeroesFromIndex(a: array<int>, idx: int): bool
  requires 0 <= idx <= a.Length
  reads a
  decreases a.Length - idx
  ensures AllZeroesFromIndex(a, idx) <==> (forall i :: idx <= i < a.Length ==> a[i] == 0)
{
  if idx == a.Length then true
  else a[idx] == 0 && AllZeroesFromIndex(a, idx + 1)
}
// </vc-helpers>

// <vc-spec>
method MoveZeroes(xs: array<int>) returns (result: array<int>)
    ensures
        /* All non-zero elements must maintain their relative order */
        IsSubsequence(FilterNonZero(xs[0..xs.Length]), result[0..result.Length])
        /* All zeroes must be located at the end of the output array */
        && (forall i :: 0 <= i < result.Length && result[i] != 0 ==> 
            forall j :: i < j < result.Length ==> result[j] != 0)
        /* The output must contain the same number of elements */
        && xs.Length == result.Length
        /* The number of zeroes must remain unchanged */
        && CountVal(0, xs[0..xs.Length]) == CountVal(0, result[0..result.Length])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): Fix loop bounds and invariants */ 
  result := new int[xs.Length];
  var zeroCount := CountVal(0, xs[0..xs.Length]);
  var nonZeroCount := xs.Length - zeroCount;
  
  var writePtr := 0;
  
  var i := 0;
  while i < xs.Length
    invariant 0 <= writePtr <= i <= xs.Length
    invariant writePtr <= nonZeroCount
    invariant forall j :: 0 <= j < writePtr ==> result[j] != 0
    invariant forall j :: 0 <= j < i ==> (j < writePtr ==> result[j] == xs[j] && result[j] != 0) || (j >= writePtr ==> result[j] == 0)
    invariant CountVal(0, result[0..i]) + CountVal(0, xs[i..xs.Length]) == CountVal(0, xs[0..xs.Length])
  {
    if xs[i] != 0 {
      result[writePtr] := xs[i];
      writePtr := writePtr + 1;
    } else {
      result[i] := 0;
    }
    i := i + 1;
  }
  
  // Fill remaining positions with zeros
  var j := writePtr;
  while j < xs.Length
    invariant writePtr <= j <= xs.Length
    invariant forall k :: 0 <= k < writePtr ==> result[k] != 0
    invariant forall k :: writePtr <= k < j ==> result[k] == 0
    invariant forall k :: j <= k < xs.Length ==> result[k] == xs[k]
  {
    result[j] := 0;
    j := j + 1;
  }
}
// </vc-code>
