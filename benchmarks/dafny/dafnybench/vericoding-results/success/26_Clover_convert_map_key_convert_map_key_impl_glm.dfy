

// <vc-helpers>
// No helpers needed for this fix
// </vc-helpers>

// <vc-spec>
method convert_map_key(inputs: map<nat, bool>, f: nat->nat) returns(r:map<nat, bool>)
  requires forall n1: nat, n2: nat :: n1 != n2 ==> f(n1) != f(n2)
  ensures forall k :: k in inputs <==> f(k) in r
  ensures forall k :: k in inputs ==> r[f(k)] == inputs[k]
// </vc-spec>
// <vc-code>
{
  var processed: set<nat> := {};
  r := map[];
  while processed != inputs.Keys
    invariant processed <= inputs.Keys
    invariant forall k :: k in processed ==> (f(k) in r && r[f(k)] == inputs[k])
    invariant forall x :: x in r ==> exists k :: k in processed && x == f(k)
  {
    var key :| key in inputs.Keys - processed;
    r := r[f(key) := inputs[key]];
    processed := processed + {key};
  }
  return r;
}
// </vc-code>

