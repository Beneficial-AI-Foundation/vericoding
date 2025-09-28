// <vc-preamble>
// Define the different kinds of numeric types
datatype NumericKind = Integer | UnsignedInteger | Float | Complex | String | Boolean

// Define precision levels from lowest to highest
datatype Precision = P8 | P16 | P32 | P64 | P128 | P256

// A numeric type combining kind and precision
datatype NumericType = NumericType(kind: NumericKind, precision: Precision)

// Define the maximum precision available for each numeric kind
function MaxPrecisionFor(kind: NumericKind): Precision
{
    match kind
    case Integer => P64
    case UnsignedInteger => P64
    case Float => P128
    case Complex => P256
    case String => P64  // Represents max string length handling capacity
    case Boolean => P8
}

// Define precision ordering - returns true if p1 <= p2
predicate PrecisionLE(p1: Precision, p2: Precision)
{
    match (p1, p2)
    case (P8, _) => true
    case (P16, P8) => false
    case (P16, _) => true
    case (P32, P8) => false
    case (P32, P16) => false
    case (P32, _) => true
    case (P64, P8) => false
    case (P64, P16) => false
    case (P64, P32) => false
    case (P64, _) => true
    case (P128, P256) => true
    case (P128, _) => false
    case (P256, _) => false
}

// Return the scalar type of highest precision of the same kind as the input
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 5): add lemma to prove precision relationship */
lemma PrecisionLEForMax(t: NumericType)
  ensures PrecisionLE(t.precision, MaxPrecisionFor(t.kind))
{
  match t.kind
  case Integer =>
    match t.precision
    case P8 => assert PrecisionLE(P8, P64);
    case P16 => assert PrecisionLE(P16, P64);
    case P32 => assert PrecisionLE(P32, P64);
    case P64 => assert PrecisionLE(P64, P64);
    case P128 => assert PrecisionLE(P128, P64);
    case P256 => assert PrecisionLE(P256, P64);
  case UnsignedInteger =>
    match t.precision
    case P8 => assert PrecisionLE(P8, P64);
    case P16 => assert PrecisionLE(P16, P64);
    case P32 => assert PrecisionLE(P32, P64);
    case P64 => assert PrecisionLE(P64, P64);
    case P128 => assert PrecisionLE(P128, P64);
    case P256 => assert PrecisionLE(P256, P64);
  case Float =>
    match t.precision
    case P8 => assert PrecisionLE(P8, P128);
    case P16 => assert PrecisionLE(P16, P128);
    case P32 => assert PrecisionLE(P32, P128);
    case P64 => assert PrecisionLE(P64, P128);
    case P128 => assert PrecisionLE(P128, P128);
    case P256 => assert PrecisionLE(P256, P128);
  case Complex =>
    match t.precision
    case P8 => assert PrecisionLE(P8, P256);
    case P16 => assert PrecisionLE(P16, P256);
    case P32 => assert PrecisionLE(P32, P256);
    case P64 => assert PrecisionLE(P64, P256);
    case P128 => assert PrecisionLE(P128, P256);
    case P256 => assert PrecisionLE(P256, P256);
  case String =>
    match t.precision
    case P8 => assert PrecisionLE(P8, P64);
    case P16 => assert PrecisionLE(P16, P64);
    case P32 => assert PrecisionLE(P32, P64);
    case P64 => assert PrecisionLE(P64, P64);
    case P128 => assert PrecisionLE(P128, P64);
    case P256 => assert PrecisionLE(P256, P64);
  case Boolean =>
    match t.precision
    case P8 => assert PrecisionLE(P8, P8);
    case P16 => assert PrecisionLE(P16, P8);
    case P32 => assert PrecisionLE(P32, P8);
    case P64 => assert PrecisionLE(P64, P8);
    case P128 => assert PrecisionLE(P128, P8);
    case P256 => assert PrecisionLE(P256, P8);
}
// </vc-helpers>

// <vc-spec>
method MaximumSctype(t: NumericType) returns (result: NumericType)
    ensures result.kind == t.kind  // Same kind as input
    ensures result.precision == MaxPrecisionFor(t.kind)  // Maximum precision for that kind
    ensures PrecisionLE(t.precision, result.precision)  // Result has higher or equal precision
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 5): call lemma to establish precision proof */
  result := NumericType(t.kind, MaxPrecisionFor(t.kind));
  PrecisionLEForMax(t);
}
// </vc-code>
