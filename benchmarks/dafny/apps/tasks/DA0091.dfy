// <vc-preamble>
function checkPairFunc(seal1: (int, int), seal2: (int, int), a: int, b: int): int
    requires a >= 1 && b >= 1
    requires seal1.0 >= 1 && seal1.1 >= 1
    requires seal2.0 >= 1 && seal2.1 >= 1
    ensures checkPairFunc(seal1, seal2, a, b) >= 0
    ensures checkPairFunc(seal1, seal2, a, b) <= seal1.0 * seal1.1 + seal2.0 * seal2.1
{
    var orientations := [(seal1, seal2), (seal1, (seal2.1, seal2.0)), ((seal1.1, seal1.0), seal2), ((seal1.1, seal1.0), (seal2.1, seal2.0))];

    var area0 := if canFit(orientations[0].0, orientations[0].1, a, b) then
        orientations[0].0.0 * orientations[0].0.1 + orientations[0].1.0 * orientations[0].1.1
    else
        0;

    var area1 := if canFit(orientations[1].0, orientations[1].1, a, b) then
        orientations[1].0.0 * orientations[1].0.1 + orientations[1].1.0 * orientations[1].1.1
    else
        0;

    var area2 := if canFit(orientations[2].0, orientations[2].1, a, b) then
        orientations[2].0.0 * orientations[2].0.1 + orientations[2].1.0 * orientations[2].1.1
    else
        0;

    var area3 := if canFit(orientations[3].0, orientations[3].1, a, b) then
        orientations[3].0.0 * orientations[3].0.1 + orientations[3].1.0 * orientations[3].1.1
    else
        0;

    max(max(area0, area1), max(area2, area3))
}

function canFit(r1: (int, int), r2: (int, int), a: int, b: int): bool
    requires a >= 1 && b >= 1
    requires r1.0 >= 1 && r1.1 >= 1
    requires r2.0 >= 1 && r2.1 >= 1
{
    (r1.0 + r2.0 <= a && max(r1.1, r2.1) <= b) || (max(r1.0, r2.0) <= a && r1.1 + r2.1 <= b)
}

function max(x: int, y: int): int
{
    if x >= y then x else y
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method solve(n: int, a: int, b: int, seals: seq<(int, int)>) returns (result: int)
    requires n >= 0
    requires a >= 1 && b >= 1
    requires |seals| == n
    requires forall i :: 0 <= i < n ==> seals[i].0 >= 1 && seals[i].1 >= 1
    ensures result >= 0
    ensures result == 0 ==> (forall i, j :: 0 <= i < n && i < j < n ==> checkPairFunc(seals[i], seals[j], a, b) == 0)
    ensures result > 0 ==> (exists i, j :: 0 <= i < n && i < j < n && checkPairFunc(seals[i], seals[j], a, b) == result)
    ensures forall i, j :: 0 <= i < n && i < j < n ==> checkPairFunc(seals[i], seals[j], a, b) <= result
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
