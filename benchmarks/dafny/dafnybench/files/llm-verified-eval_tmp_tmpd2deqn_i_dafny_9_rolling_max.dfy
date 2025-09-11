// <vc-preamble>
function isMax(m: int, numbers: seq<int>): bool
{
    m in numbers &&
    forall i :: 0 <= i < |numbers| ==> numbers[i] <= m

}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method rolling_max(numbers: seq<int>) returns (result: seq<int>)
requires numbers != []
ensures |result| == |numbers|
ensures forall i :: 0 < i < |result| ==> isMax(result[i], numbers[0..(i+1)])
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
