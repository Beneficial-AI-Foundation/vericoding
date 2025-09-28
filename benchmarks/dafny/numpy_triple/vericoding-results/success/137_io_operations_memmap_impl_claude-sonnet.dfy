// <vc-preamble>
// File access mode enumeration for memory mapping operations
datatype FileMode = ReadOnly | ReadWrite | WriteNew | CopyOnWrite

// Abstract predicate representing file existence and accessibility
predicate {:axiom} FileExists(filename: string)
{ true }

// Abstract function representing file size in bytes
function {:axiom} FileSize(filename: string): nat
  requires FileExists(filename)
{ 0 }
// </vc-preamble>

// <vc-helpers>
// Helper function to create a sequence of reals from file data
function CreateSequenceFromFile(filename: string, offset: nat, length: nat): seq<real>
  requires FileExists(filename)
  requires offset + length * 8 <= FileSize(filename)
  ensures |CreateSequenceFromFile(filename, offset, length)| == length
{
  seq(length, i => 0.0)
}

// Predicate to validate memory mapping parameters
predicate ValidMemmapParams(n: nat, filename: string, offset: nat)
{
  |filename| > 0 && FileExists(filename) && offset + n * 8 <= FileSize(filename)
}
// </vc-helpers>

// <vc-spec>
method Memmap(n: nat, filename: string, mode: FileMode, offset: nat) returns (result: seq<real>)
  // Preconditions: valid file path, file existence, and bounds validation
  requires |filename| > 0
  requires offset >= 0
  requires FileExists(filename)
  requires offset + n * 8 <= FileSize(filename) // Assuming 8 bytes per real
  
  // Postconditions: result properties and access mode constraints
  ensures |result| == n
  // Result contents are deterministic based on file, offset, and size
  ensures FileExists(filename) ==> |result| == n
  // For ReadOnly mode, ensure no file modification capability
  ensures mode == ReadOnly ==> FileExists(filename)
// </vc-spec>
// <vc-code>
{
  result := CreateSequenceFromFile(filename, offset, n);
}
// </vc-code>
