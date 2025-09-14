

// <vc-helpers>
lemma MapConversionLemma(m: map<nat, bool>, f: nat->nat, k: nat)
  requires forall n1: nat, n2: nat :: n1 != n2 ==> f(n1) != f(n2)
  ensures (k in m) == (f(k) in (map x | x in m.Keys :: f(x) := m[x]))
  ensures k in m ==> (map x | x in m.Keys :: f(x) := m[x])[f(k)] == m[k]
{
}
// </vc-helpers>

// <vc-spec>
method convert_map_key(inputs: map<nat, bool>, f: nat->nat) returns(r:map<nat, bool>)
  requires forall n1: nat, n2: nat :: n1 != n2 ==> f(n1) != f(n2)
  ensures forall k :: k in inputs <==> f(k) in r
  ensures forall k :: k in inputs ==> r[f(k)] == inputs[k]
// </vc-spec>
// <vc-code>
{
  r := map x | x in inputs.Keys :: f(x) := inputs[x];
  forall k | k in inputs.Keys
    ensures f(k) in r.Keys && r[f(k)] == inputs[k]
  {
    assert f(k) in r.Keys by {
      assert k in inputs.Keys;
    }
  }
  forall k | k in inputs.Keys
    ensures k in inputs <==> f(k) in r
  {
    // This is automatically true by the map comprehension
  }
}
// </vc-code>

