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
lemma CountValidTriplesForZHelperNonNeg(k: int, s: int, z: int, y: int)
    requires k >= 0
    requires z >= 0
    requires y >= 0
    ensures CountValidTriplesForZHelper(k, s, z, y) >= 0
    decreases if k >= y then k + 1 - y else 0
{
    if y > k {
        // By definition the function returns 0 when y > k
        assert CountValidTriplesForZHelper(k, s, z, y) == 0;
        assert CountValidTriplesForZHelper(k, s, z, y) >= 0;
    } else {
        var x := s - y - z;
        var thisCount := if 0 <= x <= k then 1 else 0;
        // Unfold the function definition for this case
        assert CountValidTriplesForZHelper(k, s, z, y) == thisCount + CountValidTriplesForZHelper(k, s, z, y + 1);
        // Prove the recursive tail is non-negative
        CountValidTriplesForZHelperNonNeg(k, s, z, y + 1);
        assert CountValidTriplesForZHelper(k, s, z, y + 1) >= 0;
        // thisCount is either 0 or 1, hence non-negative
        assert thisCount >= 0;
        // Sum of non-negative terms is non-negative
        assert CountValidTriplesForZHelper(k, s, z, y) >= 0;
    }
}

lemma CountValidTriplesForZNonNeg(k: int, s: int, z: int)
    requires k >= 0
    requires z >= 0
    ensures CountValidTriplesForZ(k, s, z) >= 0
{
    // CountValidTriplesForZ(k,s,z) == CountValidTriplesForZHelper(k,s,z,0)
    CountValidTriplesForZHelperNonNeg(k, s, z, 0);
    assert CountValidTriplesForZ(k, s, z) == CountValidTriplesForZHelper(k, s, z, 0);
    assert CountValidTriplesForZ(k, s, z) >= 0;
}

lemma CountValidTriplesHelperNonNeg(k: int, s: int, z: int)
    requires k >= 0
    requires z >= 0
    ensures CountValidTriplesHelper(k, s, z) >= 0
    decreases if k >= z then k + 1 - z else 0
{
    if z > k {
        // By definition the function returns 0 when z > k
        assert CountValidTriplesHelper(k, s, z) == 0;
        assert CountValidTriplesHelper(k, s, z) >= 0;
    } else {
        // Unfold definition
        assert CountValidTriplesHelper(k, s, z) == CountValidTriplesForZ(k, s, z) + CountValidTriplesHelper(k, s, z + 1);
        // Prove first summand non-negative
        CountValidTriplesForZNonNeg(k, s, z);
        assert CountValidTriplesForZ(k, s, z) >= 0;
        // Prove recursive tail non-negative
        CountValidTriplesHelperNonNeg(k, s, z + 1);
        assert CountValidTriplesHelper(k, s, z + 1) >= 0;
        // Sum is non-negative
        assert CountValidTriplesHelper(k, s, z) >= 0;
    }
}

lemma CountValidTriplesNonNeg(k: int, s: int)
    requires k >= 0
    ensures CountValidTriples(k, s) >= 0
{
    // CountValidTriples(k,s) == CountValidTriplesHelper(k,s,0)
    CountValidTriplesHelperNonNeg(k, s, 0);
    assert CountValidTriples(k, s) == CountValidTriplesHelper(k, s, 0);
    assert CountValidTriples(k, s) >= 0;
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
  CountValidTriplesNonNeg(k, s);
  count := CountValidTriples(k, s);
}
// </vc-code>

