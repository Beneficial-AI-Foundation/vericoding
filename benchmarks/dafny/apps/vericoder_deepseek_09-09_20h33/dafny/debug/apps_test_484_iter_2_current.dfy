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

// <vc-helpers>
lemma MaxLemma(x: int, y: int, z: int)
    ensures max(x, max(y, z)) == max(max(x, y), z)
{
}

lemma MaxLemma2(x: int, y: int, z: int, w: int)
    ensures max(max(x, y), max(z, w)) == max(max(max(x, y), z), w)
{
}

lemma MaxZeroLemma(x: int, y: int)
    requires x >= 0 && y >= 0
    ensures max(x, y) >= 0
{
}

lemma CheckPairNonNegative(seal1: (int, int), seal2: (int, int), a: int, b: int)
    requires a >= 1 && b >= 1
    requires seal1.0 >= 1 && seal1.1 >= 1
    requires seal2.0 >= 1 && seal2.1 >= 1
    ensures checkPairFunc(seal1, seal2, a, b) >= 0
{
}

lemma CheckPairUpperBound(seal1: (int, int), seal2: (int, int), a: int, b: int)
    requires a >= 1 && b >= 1
    requires seal1.0 >= 1 && seal1.1 >= 1
    requires seal2.0 >= 1 && seal2.1 >= 1
    ensures checkPairFunc(seal1, seal2, a, b) <= seal1.0 * seal1.1 + seal2.0 * seal2.1
{
}

lemma CheckPairZeroLemma(seal1: (int, int), seal2: (int, int), a: int, b: int)
    requires a >= 1 && b >= 1
    requires seal1.0 >= 1 && seal1.1 >= 1
    requires seal2.0 >= 1 && seal2.1 >= 1
    ensures checkPairFunc(seal1, seal2, a, b) == 0 ==> !canFit(seal1, seal2, a, b) && !canFit(seal1, (seal2.1, seal2.0), a, b) && !canFit((seal1.1, seal1.0), seal2, a, b) && !canFit((seal1.1, seal1.0), (seal2.1, seal2.0), a, b)
{
}
// </vc-helpers>
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
    result := 0;
    var i := 0;
    while i < n
        invariant 0 <= i <= n
        invariant result >= 0
        invariant forall x, y :: 0 <= x < i && x < y < n ==> checkPairFunc(seals[x], seals[y], a, b) <= result
        invariant result == 0 ==> forall x, y :: 0 <= x < i && x < y < n ==> checkPairFunc(seals[x], seals[y], a, b) == 0
        invariant result > 0 ==> exists x, y :: 0 <= x < i && x < y < n && checkPairFunc(seals[x], seals[y], a, b) == result
    {
        var j := i + 1;
        while j < n
            invariant i + 1 <= j <= n
            invariant result >= 0
            invariant forall x, y :: 0 <= x < i && x < y < n ==> checkPairFunc(seals[x], seals[y], a, b) <= result
            invariant forall y :: i < y < j ==> checkPairFunc(seals[i], seals[y], a, b) <= result
            invariant result == 0 ==> forall x, y :: 0 <= x < i && x < y < n ==> checkPairFunc(seals[x], seals[y], a, b) == 0
            invariant result == 0 ==> forall y :: i < y < j ==> checkPairFunc(seals[i], seals[y], a, b) == 0
            invariant result > 0 ==> exists x, y :: 0 <= x < i && x < y < n && checkPairFunc(seals[x], seals[y], a, b) == result
        {
            var pairArea := checkPairFunc(seals[i], seals[j], a, b);
            if pairArea > 0 {
                if result == 0 || pairArea > result {
                    result := pairArea;
                }
            } else {
                assert pairArea == 0;
            }
            j := j + 1;
        }
        if result > 0 {
            assert exists x, y :: 0 <= x < i && x < y < n && checkPairFunc(seals[x], seals[y], a, b) == result;
        }
        i := i + 1;
    }
}
// </vc-code>

