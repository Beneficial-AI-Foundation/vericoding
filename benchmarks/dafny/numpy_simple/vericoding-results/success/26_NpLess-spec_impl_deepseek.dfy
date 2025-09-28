// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Add reads clauses to array access functions */
function LessThan(i: int, a: array<int>, b: array<int>): bool
  requires 0 <= i < a.Length && a.Length == b.Length
  reads a, b
{
  a[i] < b[i]
}

function ArrayLess(a: array<int>, b: array<int>, length: int): (r: seq<bool>)
  requires 0 <= length <= a.Length && a.Length == b.Length
  reads a, b
  ensures |r| == length
  ensures forall i :: 0 <= i < length ==> r[i] == (a[i] < b[i])
{
  if length == 0 then []
  else ArrayLess(a, b, length - 1) + [a[length - 1] < b[length - 1]]
}
// </vc-helpers>

// <vc-spec>
method Less(a: array<int>, b: array<int>) returns (result: array<bool>)
    requires a.Length == b.Length
    ensures result.Length == a.Length
    ensures forall i :: 0 <= i < a.Length ==> result[i] == (a[i] < b[i])
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Use compiled helper function with proper array reads */
{
    result := new bool[a.Length];
    var index := 0;
    while index < a.Length
        invariant 0 <= index <= a.Length
        invariant result.Length == a.Length
        invariant forall i :: 0 <= i < index ==> result[i] == (a[i] < b[i])
    {
        result[index] := a[index] < b[index];
        index := index + 1;
    }
}
// </vc-code>
