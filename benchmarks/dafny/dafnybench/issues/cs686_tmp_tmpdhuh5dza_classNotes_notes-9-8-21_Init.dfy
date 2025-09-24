// <vc-preamble>
// Forall

// Quantifiers
class Secret{
    var secret : int;
    var known : bool;
    var count : int;
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method Init(x : int)
    modifies `secret, `known, `count
    requires 1 <= x <= 10
    ensures secret == x
    ensures known == false
    ensures count == 0
// </vc-spec>
// <vc-code>
{
        known := false;
        count := 0;
        secret := x;
}
// </vc-code>

}