// <vc-preamble>
// Enumeration of supported integer types
datatype IntType = 
    | Int8
    | Int16  
    | Int32
    | Int64
    | UInt8
    | UInt16
    | UInt32
    | UInt64

// Integer type information structure containing machine limits
datatype IntInfo = IntInfo(
    bits: nat,  // Number of bits occupied by the type
    min: int,   // Smallest integer expressible by the type  
    max: int    // Largest integer expressible by the type
)

// Returns machine limits for the specified integer type
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method iinfo(int_type: IntType) returns (info: IntInfo)
    ensures match int_type {
        case Int8 => info.bits == 8 && info.min == -128 && info.max == 127
        case Int16 => info.bits == 16 && info.min == -32768 && info.max == 32767
        case Int32 => info.bits == 32 && info.min == -2147483648 && info.max == 2147483647
        case Int64 => info.bits == 64 && info.min == -9223372036854775808 && info.max == 9223372036854775807
        case UInt8 => info.bits == 8 && info.min == 0 && info.max == 255
        case UInt16 => info.bits == 16 && info.min == 0 && info.max == 65535
        case UInt32 => info.bits == 32 && info.min == 0 && info.max == 4294967295
        case UInt64 => info.bits == 64 && info.min == 0 && info.max == 18446744073709551615
    }
// </vc-spec>
// <vc-code>
{
  match int_type {
    case Int8 => info := IntInfo(8, -128, 127);
    case Int16 => info := IntInfo(16, -32768, 32767);
    case Int32 => info := IntInfo(32, -2147483648, 2147483647);
    case Int64 => info := IntInfo(64, -9223372036854775808, 9223372036854775807);
    case UInt8 => info := IntInfo(8, 0, 255);
    case UInt16 => info := IntInfo(16, 0, 65535);
    case UInt32 => info := IntInfo(32, 0, 4294967295);
    case UInt64 => info := IntInfo(64, 0, 18446744073709551615);
  }
}
// </vc-code>
