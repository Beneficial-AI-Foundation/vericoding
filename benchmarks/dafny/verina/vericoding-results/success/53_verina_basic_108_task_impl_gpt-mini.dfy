// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 3): recursive function computing prefix sum up to j */
function SumUpTo(ops: seq<int>, j: int): int
  requires 0 <= j <= |ops|
  decreases j
{
  if j == 0 then 0 else SumUpTo(ops, j-1) + ops[j-1]
}

/* helper modified by LLM (iteration 3): predicate to detect negative prefix sums */
predicate HasNegativePrefix(s: seq<int>)
{
  exists i :: 1 <= i < |s| && s[i] < 0
}
// </vc-helpers>

// <vc-spec>
method BelowZero(operations: array<int>) returns (result: (array<int>, bool))
    ensures
        result.0.Length == operations.Length + 1
    ensures
        result.0[0] == 0
    ensures
        forall i :: 0 <= i < operations.Length ==> result.0[i + 1] == result.0[i] + operations[i]
    ensures
        result.1 == (exists i :: 1 <= i < result.0.Length && result.0[i] < 0)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 3): compute prefix sums array and detect negative prefix */
  var n := operations.Length;
  var sums := new int[n + 1];
  sums[0] := 0;
  var found := false;
  var acc := 0;
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant sums.Length == n + 1
    invariant sums[0] == 0
    invariant forall k :: 0 <= k <= i ==> sums[k] == (if k == 0 then 0 else sums[k-1] + operations[k-1])
    invariant acc == sums[i]
    invariant found == (exists k :: 1 <= k <= i && sums[k] < 0)
  {
    acc := acc + operations[i];
    sums[i + 1] := acc;
    if acc < 0 {
      found := true;
    }
    i := i + 1;
  }
  result := (sums, found);
}
// </vc-code>
