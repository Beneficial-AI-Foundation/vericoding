predicate ValidInput(k: int, s: int) {
    k >= 0 && s >= 0 && s <= 3 * k
}

predicate IsValidTriple(k: int, s: int, x: int, y: int, z: int) {
    0 <= x <= k && 0 <= y <= k && 0 <= z <= k && x + y + z == s
}

function CountValidTriples(k: int, s: int): int
    requires k >= 0
{
    CountValidTriplesHelper(k, s, 0)
}

function CountValidTriplesHelper(k: int, s: int, z: int): int
    requires k >= 0
    requires z >= 0
    decreases if k >= z then k + 1 - z else 0
{
    if z > k then 0
    else CountValidTriplesForZ(k, s, z) + CountValidTriplesHelper(k, s, z + 1)
}

function CountValidTriplesForZ(k: int, s: int, z: int): int
    requires k >= 0
    requires z >= 0
{
    CountValidTriplesForZHelper(k, s, z, 0)
}

function CountValidTriplesForZHelper(k: int, s: int, z: int, y: int): int
    requires k >= 0
    requires z >= 0
    requires y >= 0
    decreases if k >= y then k + 1 - y else 0
{
    if y > k then 0
    else 
        var x := s - y - z;
        var thisCount := if 0 <= x <= k then 1 else 0;
        thisCount + CountValidTriplesForZHelper(k, s, z, y + 1)
}

// <vc-helpers>
lemma CountValidTriplesForZHelperIsNonNegative(k: int, s: int, z: int, y: int)
    requires k >= 0 && z >= 0 && y >= 0
    decreases if k >= y then k + 1 - y else 0
    ensures CountValidTriplesForZHelper(k, s, z, y) >= 0
{
    if y <= k {
        var x := s - y - z;
        var thisCount := if 0 <= x <= k then 1 else 0;
        assert thisCount >= 0;
        CountValidTriplesForZHelperIsNonNegative(k, s, z, y + 1);
    }
}

lemma CountValidTriplesForZIsNonNegative(k: int, s: int, z: int)
    requires k >= 0 && z >= 0
    ensures CountValidTriplesForZ(k, s, z) >= 0
{
    CountValidTriplesForZHelperIsNonNegative(k, s, z, 0);
}

lemma CountValidTriplesHelperIsNonNegative(k: int, s: int, z: int)
    requires k >= 0 && z >= 0
    decreases if k >= z then k + 1 - z else 0
    ensures CountValidTriplesHelper(k, s, z) >= 0
{
    if z <= k {
        CountValidTriplesForZIsNonNegative(k, s, z);
        CountValidTriplesHelperIsNonNegative(k, s, z + 1);
    }
}

lemma CountValidTriplesIsNonNegative(k: int, s: int)
    requires k >= 0
    ensures CountValidTriples(k, s) >= 0
{
    CountValidTriplesHelperIsNonNegative(k, s, 0);
}
// </vc-helpers>

// <vc-spec>
method CountTriples(k: int, s: int) returns (count: int)
    requires ValidInput(k, s)
    ensures count == CountValidTriples(k, s)
    ensures count >= 0
// </vc-spec>
// <vc-code>
{
    CountValidTriplesIsNonNegative(k, s);
    return CountValidTriples(k, s);
}
// </vc-code>

