// <vc-preamble>
const PI: real := 3.14159265358979323846
// </vc-preamble>

// <vc-helpers>
function ValidateConversion(deg: real, rad: real): bool
{
    rad == deg * (PI / 180.0)
}

lemma ConversionLemma(deg: real)
    ensures ValidateConversion(deg, deg * (PI / 180.0))
{
}

lemma ZeroConversion()
    ensures ValidateConversion(0.0, 0.0)
{
}

lemma NinetyConversion()
    ensures ValidateConversion(90.0, PI / 2.0)
{
}

lemma OneEightyConversion()
    ensures ValidateConversion(180.0, PI)
{
}

lemma TwoSeventyConversion()
    ensures ValidateConversion(270.0, 3.0 * PI / 2.0)
{
}

lemma ThreeSixtyConversion()
    ensures ValidateConversion(360.0, 2.0 * PI)
{
}

lemma NegativeNinetyConversion()
    ensures ValidateConversion(-90.0, -PI / 2.0)
{
}

lemma NegativeOneEightyConversion()
    ensures ValidateConversion(-180.0, -PI)
{
}

lemma PeriodicityLemma(deg: real)
    ensures ValidateConversion(deg + 360.0, deg * (PI / 180.0) + 2.0 * PI)
{
}
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
  /* code modified by LLM (iteration 2): Fixed array/seq type mismatch */
  var n := |degrees|;
  radians := [];
  var i := 0;
  
  while i < n
    invariant 0 <= i <= n
    invariant |radians| == i
    invariant forall j :: 0 <= j < i ==> radians[j] == degrees[j] * (PI / 180.0)
  {
    radians := radians + [degrees[i] * (PI / 180.0)];
    i := i + 1;
  }
}
// </vc-code>
