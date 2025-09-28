// <vc-preamble>
/*
 * numpy.isdtype: Determine if a provided dtype is of a specified data type kind.
 * 
 * This module implements NumPy's dtype kind classification system, checking whether
 * a given NumPy dtype belongs to a specified category of data types such as 'bool',
 * 'signed integer', 'unsigned integer', 'integral', 'real floating', 'complex floating',
 * and 'numeric'. The function performs type introspection and classification of NumPy
 * dtypes according to their fundamental characteristics.
 */

// NumPy data type representation
datatype NumpyDType = 
    | Bool          // Boolean data type
    | Int8          // 8-bit signed integer
    | Int16         // 16-bit signed integer  
    | Int32         // 32-bit signed integer
    | Int64         // 64-bit signed integer
    | UInt8         // 8-bit unsigned integer
    | UInt16        // 16-bit unsigned integer
    | UInt32        // 32-bit unsigned integer
    | UInt64        // 64-bit unsigned integer
    | Float16       // 16-bit floating point
    | Float32       // 32-bit floating point
    | Float64       // 64-bit floating point
    | Complex64     // 64-bit complex number
    | Complex128    // 128-bit complex number

// NumPy data type kind categories
datatype DTypeKind = 
    | Bool              // Boolean kind
    | SignedInteger     // Signed integer kind
    | UnsignedInteger   // Unsigned integer kind
    | Integral          // Any integer kind (signed or unsigned)
    | RealFloating      // Real floating point kind
    | ComplexFloating   // Complex floating point kind
    | Numeric           // Any numeric kind

// Get the fundamental kind of a NumPy dtype
function getDTypeKind(dtype: NumpyDType): DTypeKind
{
    match dtype
    case Bool => DTypeKind.Bool
    case Int8 | Int16 | Int32 | Int64 => DTypeKind.SignedInteger
    case UInt8 | UInt16 | UInt32 | UInt64 => DTypeKind.UnsignedInteger
    case Float16 | Float32 | Float64 => DTypeKind.RealFloating
    case Complex64 | Complex128 => DTypeKind.ComplexFloating
}

// Check if a NumPy dtype belongs to a specific kind category
function isOfKind(dtype: NumpyDType, kind: DTypeKind): bool
{
    match kind
    case Bool => getDTypeKind(dtype) == DTypeKind.Bool
    case SignedInteger => getDTypeKind(dtype) == DTypeKind.SignedInteger
    case UnsignedInteger => getDTypeKind(dtype) == DTypeKind.UnsignedInteger
    case Integral => getDTypeKind(dtype) == DTypeKind.SignedInteger || getDTypeKind(dtype) == DTypeKind.UnsignedInteger
    case RealFloating => getDTypeKind(dtype) == DTypeKind.RealFloating
    case ComplexFloating => getDTypeKind(dtype) == DTypeKind.ComplexFloating
    case Numeric => getDTypeKind(dtype) in {DTypeKind.Bool, DTypeKind.SignedInteger, DTypeKind.UnsignedInteger, DTypeKind.RealFloating, DTypeKind.ComplexFloating}
}

// Main function: Check if a dtype belongs to a specified kind category
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method numpy_isdtype(dtype: NumpyDType, kind: DTypeKind) returns (result: bool)
    ensures result == isOfKind(dtype, kind)
// </vc-spec>
// <vc-code>
{
  result := isOfKind(dtype, kind);
}
// </vc-code>
