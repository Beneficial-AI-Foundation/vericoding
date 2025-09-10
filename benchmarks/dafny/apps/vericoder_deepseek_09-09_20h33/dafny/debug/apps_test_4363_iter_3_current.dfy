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
lemma CountValidTriplesForZHelperCompletes(k: int, s: int, z: int)
    requires k >= 0 && z >= 0
    ensures forall y | y > k :: CountValidTriplesForZHelper(k, s, z, y) == 0
{
}

lemma CountValidTriplesHelperCompletes(k: int, s: int)
    requires k >= 0
    ensures forall z | z > k :: CountValidTriplesHelper(k, s, z) == 0
{
}

lemma CountValidTriplesHelperCorrect(k: int, s: int, z: int)
    requires k >= 0 && z >= 0
    ensures CountValidTriplesHelper(k, s, z) >= 0
    decreases if k >= z then k + 1 - z else 0
{
    if z <= k {
        CountValidTriplesForZCorrect(k, s, z);
        CountValidTriplesHelperCorrect(k, s, z + 1);
    }
}

lemma CountValidTriplesForZCorrect(k: int, s: int, z: int)
    requires k >= 0 && z >= 0
    ensures CountValidTriplesForZ(k, s, z) >= 0
{
    CountValidTriplesForZHelperCorrect(k, s, z, 0);
}

lemma CountValidTriplesForZHelperCorrect(k: int, s: int, z: int, y: int)
    requires k >= 0 && z >= 0 && y >= 0
    ensures CountValidTriplesForZHelper(k, s, z, y) >= 0
    decreases if k >= y then k + 1 - y else 0
{
    if y <= k {
        CountValidTriplesForZHelperCorrect(k, s, z, y + 1);
    }
}

ghost function CountValidTriplesForZHelperStep(k: int, s: int, z: int, y: int): int
    requires k >= 0 && z >= 0 && y >= 0
    ensures CountValidTriplesForZHelper(k, s, z, y) == 
        (if y <= k then (if 0 <= s - y - z <= k then 1 else 0) + CountValidTriplesForZHelper(k, s, z, y + 1) else 0)
{
    if y > k {
        0
    } else {
        var x := s - y - z;
        var thisCount := if 0 <= x <= k then 1 else 0;
        thisCount + CountValidTriplesForZHelper(k, s, z, y + 1)
    }
}

ghost function CountValidTriplesHelperStep(k: int, s: int, z: int): int
    requires k >= 0 && z >= 0
    ensures CountValidTriplesHelper(k, s, z) == 
        (if z <= k then CountValidTriplesForZ(k, s, z) + CountValidTriplesHelper(k, s, z + 1) else 0)
{
    if z > k {
        0
    } else {
        CountValidTriplesForZ(k, s, z) + CountValidTriplesHelper(k, s, z + 1)
    }
}
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method CountTriples(k: int, s: int) returns (count: int)
    requires ValidInput(k, s)
    ensures count == CountValidTriples(k, s)
    ensures count >= 0
// </vc-spec>
// <vc-code>
{
    count := 0;
    var z := 0;
    while z <= k
        invariant 0 <= z <= k + 1
        invariant count == CountValidTriplesHelper(k, s, z)
        invariant count >= 0
    {
        var y := 0;
        var countZ := 0;
        while y <= k
            invariant 0 <= y <= k + 1
            invariant countZ == CountValidTriplesForZHelper(k, s, z, y)
            invariant countZ >= 0
        {
            var x := s - y - z;
            if 0 <= x <= k {
                countZ := countZ + 1;
            }
            y := y + 1;
            assert countZ == CountValidTriplesForZHelper(k, s, z, y) by {
                calc {
                    countZ;
                    == CountValidTriplesForZHelper(k, s, z, y - 1);
                    == (if 0 <= s - (y-1) - z <= k then 1 else 0) + CountValidTriplesForZHelper(k, s, z, y);
                }
            }
        }
        assert countZ == CountValidTriplesForZ(k, s, z);
        count := count + countZ;
        z := z + 1;
        assert count == CountValidTriplesHelper(k, s, z) by {
            calc {
                count;
                == old(count) + countZ;
                == CountValidTriplesHelper(k, s, z - 1) + CountValidTriplesForZ(k, s, z - 1);
                == CountValidTriplesHelper(k, s, z);
            }
        }
    }
}
// </vc-code>

