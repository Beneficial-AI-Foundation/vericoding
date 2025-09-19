// <vc-preamble>
// NumPy data type enumeration
datatype NumpyDType = 
  | UInt8 | UInt16 | UInt32 | UInt64
  | Int8 | Int16 | Int32 | Int64
  | Float16 | Float32 | Float64
  | Complex64 | Complex128

// Returns the size of a data type in bits
function dtype_size(dt: NumpyDType): nat
{
  match dt
  case UInt8 => 8
  case UInt16 => 16
  case UInt32 => 32
  case UInt64 => 64
  case Int8 => 8
  case Int16 => 16
  case Int32 => 32
  case Int64 => 64
  case Float16 => 16
  case Float32 => 32
  case Float64 => 64
  case Complex64 => 64
  case Complex128 => 128
}

// Returns the kind order for type preference (lower is preferred)
function dtype_kind_order(dt: NumpyDType): nat
{
  match dt
  case UInt8 | UInt16 | UInt32 | UInt64 => 0  // unsigned integers first
  case Int8 | Int16 | Int32 | Int64 => 1      // signed integers second
  case Float16 | Float32 | Float64 => 2       // floats third
  case Complex64 | Complex128 => 3            // complex last
}

// Checks if a data type can represent a given value
predicate can_represent_value(dt: NumpyDType, value: real)
{
  match dt
  case UInt8 => 0.0 <= value <= 255.0 && value == value as int as real
  case UInt16 => 0.0 <= value <= 65535.0 && value == value as int as real
  case UInt32 => 0.0 <= value <= 4294967295.0 && value == value as int as real
  case UInt64 => 0.0 <= value <= 18446744073709551615.0 && value == value as int as real
  case Int8 => -128.0 <= value <= 127.0 && value == value as int as real
  case Int16 => -32768.0 <= value <= 32767.0 && value == value as int as real
  case Int32 => -2147483648.0 <= value <= 2147483647.0 && value == value as int as real
  case Int64 => -9223372036854775808.0 <= value <= 9223372036854775807.0 && value == value as int as real
  case Float16 => -65504.0 <= value <= 65504.0
  case Float32 => -3.4028235e38 <= value <= 3.4028235e38
  case Float64 => -1.7976931348623157e308 <= value <= 1.7976931348623157e308
  case Complex64 => -3.4028235e38 <= value <= 3.4028235e38
  case Complex128 => -1.7976931348623157e308 <= value <= 1.7976931348623157e308
}

// Determines the minimal NumPy data type that can hold the given scalar value
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method min_scalar_type(value: real) returns (result: NumpyDType)
  ensures can_represent_value(result, value)
  ensures forall dt :: dtype_size(dt) < dtype_size(result) ==> !can_represent_value(dt, value)
  ensures forall dt :: dtype_size(dt) == dtype_size(result) && can_represent_value(dt, value) ==> dtype_kind_order(result) <= dtype_kind_order(dt)
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
