method convert_map_key(inputs: map<nat, bool>, f: nat->nat) returns(r:map<nat, bool>)
  requires forall n1: nat, n2: nat :: n1 != n2 ==> f(n1) != f(n2)
  ensures forall k :: k in inputs <==> f(k) in r
  ensures forall k :: k in inputs ==> r[f(k)] == inputs[k]
// </vc-spec>
// <vc-code>
{
  r := map[];
  var keys := inputs.Keys;
  
  while keys != {}
    invariant keys <= inputs.Keys
    invariant forall k :: k in inputs.Keys - keys <==> f(k) in r
    invariant forall k :: k in inputs.Keys - keys ==> r[f(k)] == inputs[k]
    invariant forall k :: k in r ==> exists k' :: k' in inputs.Keys - keys && k == f(k')
    decreases |keys|
  {
    var k :| k in keys;
    assert k in inputs.Keys;
    assert k in inputs;
    r := r[f(k) := inputs[k]];
    keys := keys - {k};
  }
}
// </vc-code>