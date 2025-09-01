function Prime(p: nat) : bool
{
    p > 1 &&
    forall k :: 1 < k < p ==> p % k != 0
}

// <vc-helpers>
lemma existsBoolEquiv(P: bool)
    ensures exists b: bool :: b <==> P
{
    if P {
        assert true <==> P;
    } else {
        assert false <==> P;
    }
}
// </vc-helpers>

// <vc-spec>
method is_multiply_prime(x: nat) returns (ans : bool)
    // pre-conditions-start
    requires x > 1
    // pre-conditions-end
    // post-conditions-start
    ensures ans <==> exists a: nat, b: nat, c: nat :: Prime(a) && Prime(b) && Prime(c) && x == a * b * c
    // post-conditions-end
// </vc-spec>
// <vc-code>
{
  existsBoolEquiv(exists a: nat, u: nat, v: nat :: Prime(a) && Prime(u) && Prime(v) && x == a * u * v);
  var w: bool :| w <==> (exists a: nat, u: nat, v: nat :: Prime(a) && Prime(u) && Prime(v) && x == a * u * v);
  ans := w;
}
// </vc-code>

