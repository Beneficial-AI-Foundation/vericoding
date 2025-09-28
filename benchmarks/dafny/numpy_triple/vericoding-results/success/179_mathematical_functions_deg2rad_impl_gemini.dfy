// <vc-preamble>
const PI: real := 3.14159265358979323846
// </vc-preamble>

// <vc-helpers>
function DegToRad(d: real): real { d * (PI / 180.0) }
// </vc-helpers>

// <vc-spec>
method deg2rad(degrees: seq<real>) returns (radians: seq<real>)
    // The output sequence has the same length as the input sequence
    ensures |radians| == |degrees|
    
    // Basic conversion formula: each radian value equals degree value * π/180
    ensures forall i :: 0 <= i < |degrees| ==> 
        radians[i] == degrees[i] * (PI / 180.0)
    
    // Standard conversion points (sanity checks)
    ensures forall i :: 0 <= i < |degrees| ==>
        (degrees[i] == 0.0 ==> radians[i] == 0.0)
    
    ensures forall i :: 0 <= i < |degrees| ==>
        (degrees[i] == 90.0 ==> radians[i] == PI / 2.0)
    
    ensures forall i :: 0 <= i < |degrees| ==>
        (degrees[i] == 180.0 ==> radians[i] == PI)
    
    ensures forall i :: 0 <= i < |degrees| ==>
        (degrees[i] == 270.0 ==> radians[i] == 3.0 * PI / 2.0)
    
    ensures forall i :: 0 <= i < |degrees| ==>
        (degrees[i] == 360.0 ==> radians[i] == 2.0 * PI)
    
    // Negative values work correctly
    ensures forall i :: 0 <= i < |degrees| ==>
        (degrees[i] == -90.0 ==> radians[i] == -PI / 2.0)
    
    ensures forall i :: 0 <= i < |degrees| ==>
        (degrees[i] == -180.0 ==> radians[i] == -PI)
    
    // Periodicity property: adding 360 degrees = adding 2π radians
    ensures forall i :: 0 <= i < |degrees| ==>
        (degrees[i] + 360.0) * (PI / 180.0) == radians[i] + 2.0 * PI
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): [Used a while loop to build the sequence, avoiding a potential compiler issue with sequence comprehensions.] */
  var rs: seq<real> := [];
  var i := 0;
  while i < |degrees|
    invariant |rs| == i
    invariant 0 <= i <= |degrees|
    invariant forall k :: 0 <= k < i ==> rs[k] == DegToRad(degrees[k])
  {
    rs := rs + [DegToRad(degrees[i])];
    i := i + 1;
  }
  radians := rs;
}
// </vc-code>
