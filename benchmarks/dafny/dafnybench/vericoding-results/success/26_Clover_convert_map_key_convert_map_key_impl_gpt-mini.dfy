

// <vc-helpers>
// (no helpers needed)
// </vc-helpers>

// <vc-spec>
method convert_map_key(inputs: map<nat, bool>, f: nat->nat) returns(r:map<nat, bool>)
  requires forall n1: nat, n2: nat :: n1 != n2 ==> f(n1) != f(n2)
  ensures forall k :: k in inputs <==> f(k) in r
  ensures forall k :: k in inputs ==> r[f(k)] == inputs[k]
// </vc-spec>
// <vc-code>
{
  var m: map<nat, bool> := map[];
  var processed: set<nat> := {};
  while processed != inputs.Keys
    invariant processed <= inputs.Keys
    invariant m.Keys == (set k | k in processed :: f(k))
    invariant forall k0 :: k0 in processed ==> m[f(k0)] == inputs[k0]
  {
    var k :| k in inputs.Keys && k !in processed;
    if f(k) in m {
      var k0 :| k0 in processed && f(k0) == f(k);
      assert k0 != k;
      assert f(k0) != f(k);
      assert f(k0) == f(k);
      assert false;
    }
    m := m[f(k) := inputs[k]];
    processed := processed + {k};
  }
  r := m;
}
// </vc-code>

