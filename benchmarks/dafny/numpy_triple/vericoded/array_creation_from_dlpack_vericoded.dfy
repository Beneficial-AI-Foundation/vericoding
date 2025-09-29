// <vc-preamble>
// Optional type for parameters that may or may not have values
datatype Option<T> = None | Some(value: T)

// Represents an object that implements the DLPack protocol
datatype DLPackObject<T> = DLPackObject(
  data: seq<T>,                    // The underlying data sequence
  has_dlpack: bool,               // Whether the object has __dlpack__ method
  has_dlpack_device: bool,        // Whether the object has __dlpack_device__ method  
  device: string                  // The device on which the object resides
)

/**
 * Creates an array from an object implementing the DLPack protocol.
 * Provides controlled copying behavior and device placement.
 */
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method from_dlpack<T>(
  x: DLPackObject<T>,           // Input DLPack-compatible object
  device: Option<string>,       // Optional device specification (must be "cpu" if provided)
  copy: Option<bool>           // Optional copy behavior control
) returns (result: seq<T>)
  // Input object must implement both required DLPack methods
  requires x.has_dlpack && x.has_dlpack_device
  // Device must be unspecified or "cpu"
  requires device.None? || (device.Some? && device.value == "cpu")
  
  // Result has same length as input data
  ensures |result| == |x.data|
  // Result contains same elements as input data in same order
  ensures forall i :: 0 <= i < |result| ==> result[i] == x.data[i]
  // When copy is explicitly false, result should be the same sequence as input data
  ensures copy.Some? && copy.value == false ==> result == x.data
// </vc-spec>
// <vc-code>
{
  result := x.data;
}
// </vc-code>
