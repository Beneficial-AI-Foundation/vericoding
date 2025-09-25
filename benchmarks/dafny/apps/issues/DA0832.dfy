// <vc-preamble>
predicate ValidInput(n: int, m: int, gates: seq<(int, int)>)
{
    n >= 1 && m >= 0 && |gates| == m &&
    forall i :: 0 <= i < |gates| ==> 1 <= gates[i].0 <= gates[i].1 <= n
}

function IntersectRanges(gates: seq<(int, int)>): (int, int)
{
    if |gates| == 0 then (1, 0)  // empty intersection
    else IntersectRangesHelper(gates, 0, (1, 1000000))
}

function IntersectRangesHelper(gates: seq<(int, int)>, index: int, current: (int, int)): (int, int)
    requires 0 <= index <= |gates|
    decreases |gates| - index
{
    if index == |gates| then current
    else 
        var newMin := if current.0 > gates[index].0 then current.0 else gates[index].0;
        var newMax := if current.1 < gates[index].1 then current.1 else gates[index].1;
        IntersectRangesHelper(gates, index + 1, (newMin, newMax))
}

function CountValidCards(n: int, gates: seq<(int, int)>): int
    requires n >= 1
{
    var intersection := IntersectRanges(gates);
    if intersection.0 <= intersection.1 && intersection.0 >= 1 && intersection.1 <= n then 
        intersection.1 - intersection.0 + 1 
    else 
        0
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method SolveGateProblem(n: int, m: int, gates: seq<(int, int)>) returns (result: int)
    requires ValidInput(n, m, gates)
    ensures result >= 0
    ensures result <= n
    ensures result == CountValidCards(n, gates)
// </vc-spec>
// <vc-code>
{
    var intersection := IntersectRanges(gates);
    if intersection.0 <= intersection.1 && intersection.0 >= 1 && intersection.1 <= n {
        result := intersection.1 - intersection.0 + 1;
    } else {
        result := 0;
    }
}
// </vc-code>
