// <vc-preamble>
// Define a Float datatype that can represent NaN for IEEE 754 compliance
datatype Float = Finite(value: real) | NaN

// Type aliases for clarity
type FloatVector = seq<Float>
type BoolVector = seq<bool>

// Predicate to check if a Float is NaN
predicate IsNaN(f: Float)
{
    f.NaN?
}

// Greater-than comparison for Float values with IEEE 754 semantics
predicate FloatGreater(x1: Float, x2: Float)
{
    match (x1, x2) {
        case (Finite(v1), Finite(v2)) => v1 > v2
        case (_, _) => false  // Any comparison involving NaN returns false
    }
}

// Main specification method for numpy.greater
// </vc-preamble>

// <vc-helpers>
function FloatGreaterFun(x1: Float, x2: Float): bool {
  match (x1, x2) {
    case (Finite(v1), Finite(v2)) => v1 > v2
    case (_, _) => false
  }
}

lemma FloatGreaterFun_equiv(x1: Float, x2: Float)
  ensures (FloatGreaterFun(x1, x2) <==> FloatGreater(x1, x2))
{
  match (x1, x2) {
    case (Finite(v1), Finite(v2)) =>
      if v1 > v2 {
        assert FloatGreaterFun(x1, x2);
        assert FloatGreater(x1, x2);
      } else {
        assert !FloatGreaterFun(x1, x2);
        assert !FloatGreater(x1, x2);
      }
    case (_, _) =>
      assert !FloatGreaterFun(x1, x2);
      assert !FloatGreater(x1, x2);
  }
}
// </vc-helpers>

// <vc-spec>
method numpy_greater(x1: FloatVector, x2: FloatVector) returns (result: BoolVector)
    // Input vectors must have the same length
    requires |x1| == |x2|
    
    // Output has the same length as inputs
    ensures |result| == |x1|
    
    // Element-wise comparison semantics: result[i] is true iff x1[i] > x2[i]
    ensures forall i :: 0 <= i < |result| ==>
        (result[i] <==> FloatGreater(x1[i], x2[i]))
    
    // Antisymmetry property: if x1[i] > x2[i] then not (x2[i] > x1[i])
    ensures forall i :: 0 <= i < |result| ==>
        (result[i] ==> !FloatGreater(x2[i], x1[i]))
    
    // IEEE 754 compliance: NaN comparisons always return false
    ensures forall i :: 0 <= i < |result| ==>
        ((IsNaN(x1[i]) || IsNaN(x2[i])) ==> result[i] == false)
    
    // Consistency with FloatGreater definition
    ensures forall i :: 0 <= i < |result| ==>
        (result[i] == FloatGreater(x1[i], x2[i]))
// </vc-spec>
// <vc-code>
{
  var n := |x1|;
  var a := new bool[n];
  var i := 0;
  while i < n
    invariant 0 <= i <= n
    invariant forall j :: 0 <= j < i ==> a[j] == FloatGreater(x1[j], x2[j])
  {
    var v := FloatGreaterFun(x1[i], x2[i]);
    a[i] := v;
    FloatGreaterFun_equiv(x1[i], x2[i]);
    assert a[i] == FloatGreater(x1[i], x2[i]);
    i := i + 1;
  }
  result := a[..];
}
// </vc-code>
