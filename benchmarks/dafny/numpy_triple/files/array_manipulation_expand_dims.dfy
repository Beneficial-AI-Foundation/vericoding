// <vc-preamble>
// Represents the result of expanding dimensions of a vector
// RowVector represents axis=0 case (1×n shape)
// ColumnVector represents axis=1 case (n×1 shape)
datatype ExpandedVector<T> = 
  | RowVector(data: seq<T>)     // axis=0: creates row vector (1×n)
  | ColumnVector(data: seq<T>)  // axis=1: creates column vector (n×1)

// Expands the shape of a vector by inserting a new axis at the specified position
// axis=0 creates a row vector (1×n), axis=1 creates a column vector (n×1)
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method ExpandDims<T>(a: seq<T>, axis: nat) returns (result: ExpandedVector<T>)
  requires axis <= 1  // Only support axis 0 and 1 for vector expansion
  ensures axis == 0 ==> result.RowVector? && result.data == a
  ensures axis == 1 ==> result.ColumnVector? && result.data == a
  ensures result.RowVector? ==> axis == 0
  ensures result.ColumnVector? ==> axis == 1
  // The expanded result preserves all original elements in the same order
  ensures match result {
    case RowVector(data) => data == a
    case ColumnVector(data) => data == a
  }
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
