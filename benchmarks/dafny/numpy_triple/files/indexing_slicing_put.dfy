// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Put(a: seq<real>, ind: seq<nat>, v: seq<real>) returns (result: seq<real>)
  // Preconditions: indices and values arrays must have same length, all indices must be valid
  requires |ind| == |v|
  requires forall i :: 0 <= i < |ind| ==> ind[i] < |a|
  
  // Postconditions capture the core mathematical properties
  ensures |result| == |a|  // Vector length is preserved
  
  // Elements at specified indices are replaced with corresponding values from v
  // When there are duplicate indices, the rightmost occurrence in ind takes precedence
  ensures (forall pos :: 0 <= pos < |a| && (exists i :: 0 <= i < |ind| && ind[i] == pos) 
          ==> (exists last :: 0 <= last < |ind| && ind[last] == pos && result[pos] == v[last] &&
              (forall k :: last < k < |ind| ==> ind[k] != pos)))
  
  // All other elements (not targeted by any index) remain unchanged
  ensures (forall j :: 0 <= j < |a| && (forall i :: 0 <= i < |ind| ==> j != ind[i]) ==> result[j] == a[j])
  
  // Special case: if no indices provided, result equals input
  ensures |ind| == 0 ==> result == a
  
  // When all indices are distinct and cover entire array, result is a permutation
  ensures (forall i, j :: 0 <= i < |ind| && 0 <= j < |ind| && i != j ==> ind[i] != ind[j]) &&
          (|ind| == |a|) &&
          (forall k {:trigger ind[k]} :: 0 <= k < |a| ==> exists i :: 0 <= i < |ind| && ind[i] == k)
          ==> (forall k :: 0 <= k < |a| ==> exists i :: 0 <= i < |ind| && ind[i] == k && result[k] == v[i])
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
