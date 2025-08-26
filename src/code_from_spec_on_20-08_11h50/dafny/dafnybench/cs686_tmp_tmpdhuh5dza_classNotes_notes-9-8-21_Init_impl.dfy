// Forall

// Quantifiers
class Secret{
    var secret : int;
    var known : bool;
    var count : int;

// <vc-helpers>
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
  secret := x;
  known := false;
  count := 0;
}
// </vc-code>

}