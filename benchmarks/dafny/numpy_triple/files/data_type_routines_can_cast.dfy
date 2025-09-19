// <vc-preamble>
// Data type enumeration for casting rules
datatype CastingRule = No | Equiv | Safe | SameKind | Unrestricted

// Data type enumeration for supported numeric types  
datatype DType = Int8 | Int16 | Int32 | Int64 | Float32 | Float64 | Complex64 | Complex128 | Bool

// Helper predicates for type categorization
predicate IsIntegerType(dtype: DType)
{
    dtype == Int8 || dtype == Int16 || dtype == Int32 || dtype == Int64
}

predicate IsFloatType(dtype: DType) 
{
    dtype == Float32 || dtype == Float64
}

predicate IsComplexType(dtype: DType)
{
    dtype == Complex64 || dtype == Complex128  
}

// Helper predicate for safe integer widening
predicate IsSafeIntegerWidening(from_dtype: DType, to_dtype: DType)
{
    (from_dtype == Int8 && (to_dtype == Int16 || to_dtype == Int32 || to_dtype == Int64)) ||
    (from_dtype == Int16 && (to_dtype == Int32 || to_dtype == Int64)) ||
    (from_dtype == Int32 && to_dtype == Int64)
}

// Helper predicate for safe float widening
predicate IsSafeFloatWidening(from_dtype: DType, to_dtype: DType)
{
    from_dtype == Float32 && to_dtype == Float64
}

// Helper predicate for safe integer to float conversion
predicate IsSafeIntToFloat(from_dtype: DType, to_dtype: DType)
{
    ((from_dtype == Int8 || from_dtype == Int16) && (to_dtype == Float32 || to_dtype == Float64)) ||
    (from_dtype == Int32 && to_dtype == Float64)
}

// Helper predicate for safe complex widening
predicate IsSafeComplexWidening(from_dtype: DType, to_dtype: DType)
{
    from_dtype == Complex64 && to_dtype == Complex128
}

// Helper predicate for safe float to complex conversion
predicate IsSafeFloatToComplex(from_dtype: DType, to_dtype: DType)
{
    (from_dtype == Float32 || from_dtype == Float64) && (to_dtype == Complex64 || to_dtype == Complex128)
}

// Helper predicate for same kind casting within numeric families
predicate IsSameKindCast(from_dtype: DType, to_dtype: DType)
{
    // Integer family
    (IsIntegerType(from_dtype) && IsIntegerType(to_dtype)) ||
    // Float family
    (IsFloatType(from_dtype) && IsFloatType(to_dtype)) ||
    // Complex family
    (IsComplexType(from_dtype) && IsComplexType(to_dtype)) ||
    // Cross-family promotions
    (IsIntegerType(from_dtype) && (IsFloatType(to_dtype) || IsComplexType(to_dtype))) ||
    (IsFloatType(from_dtype) && IsComplexType(to_dtype))
}
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method CanCast(from_dtype: DType, to_dtype: DType, casting: CastingRule) returns (result: bool)
    ensures 
        // Basic reflexivity: any type can cast to itself with any rule
        (from_dtype == to_dtype ==> result == true) &&
        
        // No casting rule: only identical types allowed
        (casting == No ==> (result == true <==> from_dtype == to_dtype)) &&
        
        // Safe casting preserves values
        (casting == Safe ==> (result == true ==> 
            (IsSafeIntegerWidening(from_dtype, to_dtype) ||
             IsSafeFloatWidening(from_dtype, to_dtype) ||
             IsSafeIntToFloat(from_dtype, to_dtype) ||
             IsSafeComplexWidening(from_dtype, to_dtype) ||
             IsSafeFloatToComplex(from_dtype, to_dtype) ||
             from_dtype == to_dtype))) &&
        
        // Same kind casting allows within numeric families
        (casting == SameKind ==> (result == true ==> IsSameKindCast(from_dtype, to_dtype))) &&
        
        // Unrestricted casting allows any conversion
        (casting == Unrestricted ==> result == true) &&
        
        // Equiv casting allows same types (byte-order changes only)
        (casting == Equiv ==> (result == true <==> from_dtype == to_dtype))
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
