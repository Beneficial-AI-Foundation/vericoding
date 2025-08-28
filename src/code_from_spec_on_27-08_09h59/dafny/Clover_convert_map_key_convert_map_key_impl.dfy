// <vc-helpers>
lemma InjectivePreservesDistinctKeys(inputs: map<nat, bool>, f: nat->nat)
  requires forall n1: nat, n2: nat :: n1 != n2 ==> f(n1) != f(n2)
  ensures forall k1, k2 :: k1 in inputs && k2 in inputs && k1 != k2 ==> f(k1) != f(k2)
{
}

lemma MapComprehensionProperties(inputs: map<nat, bool>, f: nat->nat)
  requires forall n1: nat, n2: nat :: n1 != n2 ==> f(n1) != f(n2)
  ensures var result := map k | k in inputs :: f(k) := inputs[k];
          forall k :: k in inputs <==> f(k) in result
  ensures var result := map k | k in inputs :: f(k) := inputs[k];
          forall k :: k in inputs ==> result[f(k)] == inputs[k]
{
  var result := map k | k in inputs :: f(k) := inputs[k];
  
  forall k ensures k in inputs <==> f(k) in result {
    if k in inputs {
      assert f(k) in result;
    }
    if f(k) in result {
      assert k in inputs;
    }
  }
  
  forall k | k in inputs ensures result[f(k)] == inputs[k] {
    assert result[f(k)] == inputs[k];
  }
}
// </vc-helpers>

// <vc-spec>
// <vc-spec>
method convert_map_key(inputs: map<nat, bool>, f: nat->nat) returns(r:map<nat, bool>)
  requires forall n1: nat, n2: nat :: n1 != n2 ==> f(n1) != f(n2)
  ensures forall k :: k in inputs <==> f(k) in r
  ensures forall k :: k in inputs ==> r[f(k)] == inputs[k]
// </vc-spec>
// </vc-spec>

// <vc-code>
{
  InjectivePreservesDistinctKeys(inputs, f);
  r := map k | k in inputs :: f(k) := inputs[k];
  MapComprehensionProperties(inputs, f);
}
// </vc-code>
