// <vc-preamble>
// Enumeration of supported integer types
datatype IntegerType = Int8 | Int16 | Int32 | Int64 | UInt8 | UInt16 | UInt32 | UInt64

// Structure representing integer type information  
datatype IntegerInfo = IntegerInfo(bits: nat, min: int, max: int)

// Method that returns machine limits for the given integer type
// </vc-preamble>

// <vc-helpers>
function computeBits(intType: IntegerType): nat {
  match intType {
    case Int8 => 8
    case Int16 => 16
    case Int32 => 32
    case Int64 => 64
    case UInt8 => 8
    case UInt16 => 16
    case UInt32 => 32
    case UInt64 => 64
  }
}

function computeMin(intType: IntegerType): int {
  match intType {
    case Int8 => -128
    case Int16 => -32768
    case Int32 => -2147483648
    case Int64 => -9223372036854775808
    case UInt8 => 0
    case UInt16 => 0
    case UInt32 => 0
    case UInt64 => 0
  }
}

function computeMax(intType: IntegerType): int {
  match intType {
    case Int8 => 127
    case Int16 => 32767
    case Int32 => 2147483647
    case Int64 => 9223372036854775807
    case UInt8 => 255
    case UInt16 => 65535
    case UInt32 => 4294967295
    case UInt64 => 18446744073709551615
  }
}
// </vc-helpers>

// <vc-spec>
method iinfo(intType: IntegerType) returns (info: IntegerInfo)
    ensures match intType {
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
  var bits := computeBits(intType);
  var min_val := computeMin(intType);
  var max_val := computeMax(intType);
  info := IntegerInfo(bits, min_val, max_val);
}
// </vc-code>
