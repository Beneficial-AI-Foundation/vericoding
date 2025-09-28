// <vc-preamble>
predicate ValidInput(n: int, m: int, pairs: seq<(int, int)>)
{
    n >= 2 && 
    m >= 0 && 
    |pairs| == m &&
    (forall i :: 0 <= i < |pairs| ==> 1 <= pairs[i].0 <= n && 1 <= pairs[i].1 <= n) &&
    (forall i :: 0 <= i < |pairs| ==> pairs[i].0 != pairs[i].1)
}

function computeFinalL(pairs: seq<(int, int)>): int
{
    if |pairs| == 0 then 1
    else 
        var x := pairs[|pairs|-1].0;
        var y := pairs[|pairs|-1].1;
        var minVal := if x < y then x else y;
        var restL := computeFinalL(pairs[..|pairs|-1]);
        if restL > minVal then restL else minVal
}

function computeFinalR(n: int, pairs: seq<(int, int)>): int
{
    if |pairs| == 0 then n
    else
        var x := pairs[|pairs|-1].0;
        var y := pairs[|pairs|-1].1;
        var maxVal := if x > y then x else y;
        var restR := computeFinalR(n, pairs[..|pairs|-1]);
        if restR < maxVal then restR else maxVal
}

function max(a: int, b: int): int
{
    if a > b then a else b
}

predicate ValidResult(n: int, pairs: seq<(int, int)>, result: int)
{
    result >= 0 &&
    result <= n - 1 &&
    result == max(computeFinalR(n, pairs) - computeFinalL(pairs), 0)
}
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): The original functions `computeFinalL`, `computeFinalR`, `max` are already defined in the preamble. I had duplicated them as `ComputeFinalL`, `ComputeFinalR`, `ComputeMax` in the previous turn, which caused compilation errors. In this turn, I removed the helper functions to avoid redundancy and rely on the already defined functions. */
// </vc-helpers>

// <vc-spec>
method solve(n: int, m: int, pairs: seq<(int, int)>) returns (result: int)
    requires ValidInput(n, m, pairs)
    ensures ValidResult(n, pairs, result)
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): The previous implementation was attempting to call helper functions that were not correctly defined (they were duplicates of preamble functions). I have removed the now-redundant helper definitions, and in this turn, the method directly calls the functions already defined in the preamble (`computeFinalL`, `computeFinalR`, `max`). This resolves compilation errors and ensures all `ensures` clauses are satisfied. */
  var l := computeFinalL(pairs);
  var r := computeFinalR(n, pairs);
  result := max(r - l, 0);
}
// </vc-code>
