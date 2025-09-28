// <vc-preamble>
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 4): Added complete postcondition establishment with unscaled relation */
function integrate_coefficients(c: seq<real>, scl: real): seq<real>
  requires scl != 0.0
  requires |c| >= 0
  ensures |integrate_coefficients(c, scl)| == |c| + 1
{
  [0.0] + seq(|c|, i requires 0 <= i < |c| => c[i] * scl / (2.0 * i as real + 1.0))
}

function integrate_unscaled(c: seq<real>): seq<real>
  requires |c| >= 0
  ensures |integrate_unscaled(c)| == |c| + 1
{
  [0.0] + seq(|c|, i requires 0 <= i < |c| => c[i] / (2.0 * i as real + 1.0))
}

lemma IntegrationScalingRelation(c: seq<real>, scl: real)
  requires scl != 0.0
  requires |c| >= 0
  ensures var scaled := integrate_coefficients(c, scl);
          var unscaled := integrate_unscaled(c);
          |scaled| == |unscaled| &&
          forall i :: 0 <= i < |scaled| ==> scaled[i] == scl * unscaled[i]
{
  var scaled := integrate_coefficients(c, scl);
  var unscaled := integrate_unscaled(c);
  assert |scaled| == |c| + 1 == |unscaled|;
  
  assert scaled[0] == 0.0 == scl * 0.0 == scl * unscaled[0];
  
  forall i | 1 <= i < |scaled|
    ensures scaled[i] == scl * unscaled[i]
  {
    assert scaled[i] == c[i-1] * scl / (2.0 * (i-1) as real + 1.0);
    assert unscaled[i] == c[i-1] / (2.0 * (i-1) as real + 1.0);
    assert scaled[i] == scl * unscaled[i];
  }
}
// </vc-helpers>

// <vc-spec>
method legint(c: seq<real>, k: real, lbnd: real, scl: real) returns (result: seq<real>)
    requires scl != 0.0
    requires |c| >= 0
    ensures |result| == |c| + 1
    ensures |c| == 0 ==> result == [k]
    ensures |c| > 0 ==> (
        // Integration constant affects the constant term
        exists base_result: seq<real> :: (|base_result| == |c| + 1 &&
        result[0] == base_result[0] + k &&
        (forall i {:trigger result[i]} :: 1 <= i < |result| ==> result[i] == base_result[i]) &&
        
        // Scaling factor affects all integrated coefficients consistently  
        (scl != 1.0 ==> exists unscaled: seq<real> :: (|unscaled| == |c| + 1 &&
            forall i {:trigger base_result[i]} :: 0 <= i < |result| ==> base_result[i] == scl * unscaled[i])))
    )
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 4): Establish complete postcondition with base_result and unscaled */
{
  if |c| == 0 {
    result := [k];
  } else {
    var integrated := integrate_coefficients(c, scl);
    result := seq(|integrated|, i requires 0 <= i < |integrated| => 
                  if i == 0 then integrated[0] + k else integrated[i]);
    
    assert |result| == |c| + 1;
    assert result[0] == integrated[0] + k;
    assert forall i :: 1 <= i < |result| ==> result[i] == integrated[i];
    
    // Establish base_result existence
    ghost var base_result := integrated;
    assert |base_result| == |c| + 1;
    assert result[0] == base_result[0] + k;
    assert forall i :: 1 <= i < |result| ==> result[i] == base_result[i];
    
    // Establish unscaled existence when scl != 1.0
    if scl != 1.0 {
      ghost var unscaled := integrate_unscaled(c);
      IntegrationScalingRelation(c, scl);
      assert |unscaled| == |c| + 1;
      assert forall i :: 0 <= i < |base_result| ==> base_result[i] == scl * unscaled[i];
    }
  }
}
// </vc-code>
