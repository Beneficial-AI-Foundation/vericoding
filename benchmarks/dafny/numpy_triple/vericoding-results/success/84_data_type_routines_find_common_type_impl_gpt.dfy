// <vc-preamble>
/* This file implements the specification for numpy.find_common_type function
 * which determines common data type following NumPy's type promotion rules.
 * The function returns the maximum of array_types ignoring scalar_types, unless 
 * the maximum of scalar_types is of a different kind (dtype.kind).
 */

// Data type representation for NumPy types
datatype DType = 
    // 8-bit signed integer
    | int8 
    // 16-bit signed integer
    | int16 
    // 32-bit signed integer
    | int32 
    // 64-bit signed integer
    | int64
    // 8-bit unsigned integer
    | uint8 
    // 16-bit unsigned integer
    | uint16 
    // 32-bit unsigned integer
    | uint32 
    // 64-bit unsigned integer
    | uint64
    // 32-bit floating point
    | float32 
    // 64-bit floating point
    | float64
    // 64-bit complex number
    | complex64 
    // 128-bit complex number
    | complex128
    // Boolean type
    | Bool
    // Object type
    | Object

// Option type for return values
datatype Option<T> = None | Some(value: T)

// Type hierarchy for promotion rules (returns character representing the type category)
function Kind(dt: DType): char
{
    match dt
        case Bool => 'b'
        case int8 | int16 | int32 | int64 => 'i'
        case uint8 | uint16 | uint32 | uint64 => 'u'
        case float32 | float64 => 'f'
        case complex64 | complex128 => 'c'
        case Object => 'O'
}

// Type precedence for promotion (higher values have higher precedence)
function Precedence(dt: DType): nat
{
    match dt
        case Bool => 0
        case int8 => 1
        case int16 => 2
        case int32 => 3
        case int64 => 4
        case uint8 => 5
        case uint16 => 6
        case uint32 => 7
        case uint64 => 8
        case float32 => 9
        case float64 => 10
        case complex64 => 11
        case complex128 => 12
        case Object => 13
}

// Helper predicate to check if a type has maximum precedence in a sequence
ghost predicate IsMaxPrecedence(dt: DType, types: seq<DType>)
{
    dt in types && forall other :: other in types ==> Precedence(other) <= Precedence(dt)
}

// Main method implementing NumPy's find_common_type function
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method FindCommonType(array_types: seq<DType>, scalar_types: seq<DType>) returns (result: Option<DType>)
    // Precondition: At least one of the input sequences is non-empty
    requires |array_types| > 0 || |scalar_types| > 0
    
    // Case 1: Only array types provided - return maximum precedence type from array_types
    ensures (|array_types| > 0 && |scalar_types| == 0) ==>
        (result.Some? && IsMaxPrecedence(result.value, array_types))
    
    // Case 2: Only scalar types provided - return maximum precedence type from scalar_types  
    ensures (|array_types| == 0 && |scalar_types| > 0) ==>
        (result.Some? && IsMaxPrecedence(result.value, scalar_types))
    
    // Case 3: Both array and scalar types provided - follow NumPy promotion rules
    ensures (|array_types| > 0 && |scalar_types| > 0) ==>
        (exists max_array, max_scalar ::
            IsMaxPrecedence(max_array, array_types) &&
            IsMaxPrecedence(max_scalar, scalar_types) &&
            (if Kind(max_array) == Kind(max_scalar) 
             then result == Some(max_array)
             else result == Some(max_scalar)))
// </vc-spec>
// <vc-code>
{
  if |array_types| > 0 && |scalar_types| == 0 {
    var i := 1;
    var idxA := 0;
    var maxA := array_types[idxA];
    while i < |array_types|
      invariant 1 <= i <= |array_types|
      invariant 0 <= idxA < i
      invariant maxA == array_types[idxA]
      invariant forall j :: 0 <= j < i ==> Precedence(array_types[j]) <= Precedence(maxA)
      decreases |array_types| - i
    {
      if Precedence(array_types[i]) >= Precedence(maxA) {
        idxA := i;
        maxA := array_types[i];
      }
      i := i + 1;
    }
    assert 0 <= idxA < |array_types|;
    assert forall other :: other in array_types ==> Precedence(other) <= Precedence(maxA)
      by {
        forall other | other in array_types
          ensures Precedence(other) <= Precedence(maxA)
        {
          var j :| 0 <= j < |array_types| && array_types[j] == other;
          assert Precedence(array_types[j]) <= Precedence(maxA);
        }
      }
    assert IsMaxPrecedence(maxA, array_types);
    result := Some(maxA);
  } else if |array_types| == 0 && |scalar_types| > 0 {
    var i2 := 1;
    var idxS := 0;
    var maxS := scalar_types[idxS];
    while i2 < |scalar_types|
      invariant 1 <= i2 <= |scalar_types|
      invariant 0 <= idxS < i2
      invariant maxS == scalar_types[idxS]
      invariant forall j :: 0 <= j < i2 ==> Precedence(scalar_types[j]) <= Precedence(maxS)
      decreases |scalar_types| - i2
    {
      if Precedence(scalar_types[i2]) >= Precedence(maxS) {
        idxS := i2;
        maxS := scalar_types[i2];
      }
      i2 := i2 + 1;
    }
    assert 0 <= idxS < |scalar_types|;
    assert forall other :: other in scalar_types ==> Precedence(other) <= Precedence(maxS)
      by {
        forall other | other in scalar_types
          ensures Precedence(other) <= Precedence(maxS)
        {
          var j :| 0 <= j < |scalar_types| && scalar_types[j] == other;
          assert Precedence(scalar_types[j]) <= Precedence(maxS);
        }
      }
    assert IsMaxPrecedence(maxS, scalar_types);
    result := Some(maxS);
  } else {
    // Both non-empty
    var iA := 1;
    var idxA2 := 0;
    var maxA2 := array_types[idxA2];
    while iA < |array_types|
      invariant 1 <= iA <= |array_types|
      invariant 0 <= idxA2 < iA
      invariant maxA2 == array_types[idxA2]
      invariant forall j :: 0 <= j < iA ==> Precedence(array_types[j]) <= Precedence(maxA2)
      decreases |array_types| - iA
    {
      if Precedence(array_types[iA]) >= Precedence(maxA2) {
        idxA2 := iA;
        maxA2 := array_types[iA];
      }
      iA := iA + 1;
    }
    assert 0 <= idxA2 < |array_types|;
    assert forall other :: other in array_types ==> Precedence(other) <= Precedence(maxA2)
      by {
        forall other | other in array_types
          ensures Precedence(other) <= Precedence(maxA2)
        {
          var j :| 0 <= j < |array_types| && array_types[j] == other;
          assert Precedence(array_types[j]) <= Precedence(maxA2);
        }
      }
    assert IsMaxPrecedence(maxA2, array_types);

    var iS2 := 1;
    var idxS2 := 0;
    var maxS2 := scalar_types[idxS2];
    while iS2 < |scalar_types|
      invariant 1 <= iS2 <= |scalar_types|
      invariant 0 <= idxS2 < iS2
      invariant maxS2 == scalar_types[idxS2]
      invariant forall j :: 0 <= j < iS2 ==> Precedence(scalar_types[j]) <= Precedence(maxS2)
      decreases |scalar_types| - iS2
    {
      if Precedence(scalar_types[iS2]) >= Precedence(maxS2) {
        idxS2 := iS2;
        maxS2 := scalar_types[iS2];
      }
      iS2 := iS2 + 1;
    }
    assert 0 <= idxS2 < |scalar_types|;
    assert forall other :: other in scalar_types ==> Precedence(other) <= Precedence(maxS2)
      by {
        forall other | other in scalar_types
          ensures Precedence(other) <= Precedence(maxS2)
        {
          var j :| 0 <= j < |scalar_types| && scalar_types[j] == other;
          assert Precedence(scalar_types[j]) <= Precedence(maxS2);
        }
      }
    assert IsMaxPrecedence(maxS2, scalar_types);

    if Kind(maxA2) == Kind(maxS2) {
      result := Some(maxA2);
    } else {
      result := Some(maxS2);
    }
  }
}
// </vc-code>
