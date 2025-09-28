// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): Removed the helper function as it was not being used correctly and the logic can be inlined within the main method. */
// </vc-helpers>

// <vc-spec>
method ChebVander(x: seq<real>, deg: nat) returns (V: seq<seq<real>>)
    requires |x| > 0
    ensures |V| == |x|
    ensures forall i :: 0 <= i < |V| ==> |V[i]| == deg + 1
    
    // T_0(x) = 1 for all x
    ensures forall i :: 0 <= i < |V| ==> V[i][0] == 1.0
    
    // T_1(x) = x when deg >= 1
    ensures deg >= 1 ==> (forall i :: 0 <= i < |V| ==> V[i][1] == x[i])
    
    // Recurrence relation: T_{k+1}(x) = 2x*T_k(x) - T_{k-1}(x) for k >= 1
    ensures forall k, i :: 1 <= k < deg && 0 <= i < |V| ==> 
        V[i][k + 1] == 2.0 * x[i] * V[i][k] - V[i][k - 1]
    
    // Boundedness property: Chebyshev polynomials are bounded by 1 on [-1,1]
    ensures forall i, j :: (0 <= i < |V| && 0 <= j < |V[i]| && 
        -1.0 <= x[i] <= 1.0) ==> -1.0 <= V[i][j] <= 1.0
    
    // Symmetry property: T_n(-x) = (-1)^n * T_n(x)
    ensures forall i1, i2, k :: (0 <= i1 < |V| && 0 <= i2 < |V| && 0 <= k < deg + 1 &&
        x[i1] == -x[i2]) ==> 
        V[i1][k] == (if k % 2 == 0 then 1.0 else -1.0) * V[i2][k]
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 5): Fixed a compilation error regarding `new seq<real>(...)` by providing an initial value for the sequence and ensuring all `seq` initializations are done correctly. Also, removed the buggy `chebyshev_term` helper and inlined the logic. The sequence updates using `[k..k]` have been fixed to `[k]` by directly assigning values, as Dafny `seq` concatenation and slicing operations are not type-safe during element assignment like this. */
{
  var N := |x|;
  var V_prime: seq<seq<real>> := new seq<seq<real>>(N, i => new seq<real>(deg + 1, j => 0.0)); // Initialize with a default value

  for i := 0 to N - 1 {
    assert 0 <= i < N;
    assert |V_prime[i]| == deg + 1;

    if deg >= 0 {
      V_prime[i][0] := 1.0; // T_0(x) = 1
    }
    if deg >= 1 {
      V_prime[i][1] := x[i]; // T_1(x) = x
    }

    for k := 2 to deg {
      // Calculate T_k using the recurrence relation T_k(x) = 2x*T_{k-1}(x) - T_{k-2}(x)
      assert 0 <= i < N;
      assert 0 <= k - 2 < deg + 1; // k >= 2, so k-2 >= 0
      assert 0 <= k - 1 < deg + 1; // k >= 2, so k-1 >= 1
      assert 0 <= k < deg + 1;

      V_prime[i][k] := 2.0 * x[i] * V_prime[i][k - 1] - V_prime[i][k - 2];
    }
  }
  V := V_prime;
}
// </vc-code>
