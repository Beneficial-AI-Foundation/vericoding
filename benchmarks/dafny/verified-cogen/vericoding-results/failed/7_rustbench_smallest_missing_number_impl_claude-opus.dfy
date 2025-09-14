// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Fixed AllSmallerPresent and lemma to handle edge cases */
predicate AllSmallerPresent(s: array<int>, k: int)
  reads s
  requires 0 <= k
{
  forall i :: 0 <= i < k ==> exists j :: 0 <= j < s.Length && s[j] == i
}

lemma AllSmallerPresentUpTo(s: array<int>, k: int)
  requires forall i, j :: 0 <= i < j < s.Length ==> s[i] <= s[j]
  requires forall i :: 0 <= i < s.Length ==> s[i] >= 0
  requires 0 <= k <= s.Length
  requires forall i :: 0 <= i < k ==> s[i] == i
  ensures AllSmallerPresent(s, k)
{
  // The proof is automatic from the requires clause
}
// </vc-helpers>

// <vc-spec>
method SmallestMissingNumber(s: array<int>) returns (v: int)
    requires forall i, j :: 0 <= i < j < s.Length ==> s[i] <= s[j]
    requires forall i :: 0 <= i < s.Length ==> s[i] >= 0
    requires s.Length <= 100_000
    ensures 0 <= v
    ensures forall i :: 0 <= i < s.Length ==> s[i] != v
    ensures forall k {:trigger} :: 0 <= k < v ==> exists j :: 0 <= j < s.Length && s[j] == k
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed assertions and logic for proving postconditions */
{
  v := 0;
  
  while v < s.Length && s[v] == v
    invariant 0 <= v <= s.Length
    invariant forall i :: 0 <= i < v ==> s[i] == i
  {
    v := v + 1;
  }
  
  // At this point, either v == s.Length or s[v] != v
  // Prove that v is not in the array
  forall i | 0 <= i < s.Length
    ensures s[i] != v
  {
    if i < v {
      assert s[i] == i;
      assert s[i] != v;
    } else if i == v && v < s.Length {
      assert s[v] != v;  // from loop exit condition
    } else if i > v && v < s.Length {
      // s[v] != v from loop exit
      // Since array is sorted and s[v] != v:
      // If s[v] < v, then s[v] would be a duplicate of some earlier value
      // But we know s[0..v-1] = [0..v-1], so s[v] must be > v
      assert s[v] != v;
      if s[v] < v {
        // s[v] is some value k where 0 <= k < v
        // But s[k] == k from loop invariant
        // This means we have s[k] == k and s[v] == k with k < v
        // This violates sorted property since k < v but s[k] would equal s[v]
        var k := s[v];
        assert 0 <= k < v;
        assert s[k] == k;  // from loop invariant
        assert s[k] == s[v];  // both equal k
        assert k < v;  // indices are in order
        assert false;  // contradiction with sorted property (no duplicates)
      }
      assert s[v] > v;
      assert s[i] >= s[v];  // from sorted property
      assert s[i] > v;
      assert s[i] != v;
    }
  }
  
  // Prove all smaller values are present
  AllSmallerPresentUpTo(s, v);
}
// </vc-code>
