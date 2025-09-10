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
function VerifiedCountTriples(k: int, s: int): int
    // No longer needed as we are directly verifying the CountTriples method.
    // The previous implementation was a reference for the method's logic
    // but not strictly a helper for the final verified method.
    decreases 0 // Dummy decreases clause to satisfy function requirements
{
    0 // dummy return value
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
    var count := 0;
    var z := 0;

    while z <= k
        invariant 0 <= z <= k + 1
        invariant count == CountValidTriples(k, s) - CountValidTriplesHelper(k, s, z)
        decreases (k + 1) - z
    {
        var y := 0;
        var current_z_count := 0;

        while y <= k
            invariant 0 <= y <= k + 1
            invariant current_z_count == CountValidTriplesForZ(k, s, z) - CountValidTriplesForZHelper(k, s, z, y)
            decreases (k + 1) - y
        {
            var x := s - y - z;
            if 0 <= x && x <= k
            {
                current_z_count := current_z_count + 1;
            }
            y := y + 1;
        }
        count := count + current_z_count;
        z := z + 1;
    }
    return count;
}
// </vc-code>

