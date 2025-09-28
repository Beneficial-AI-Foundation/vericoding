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
/* helper modified by LLM (iteration 5): remove ensures clause from FileUnchanged predicate and add proper implementation */
// Helper function to read a real value from a file at a specific byte position
function ReadRealFromFile(filename: string, byteOffset: nat): real
  requires FileExists(filename)
  requires byteOffset + 8 <= FileSize(filename)

// Helper predicate to ensure file remains unchanged after operation
predicate FileUnchanged(filename: string, originalSize: nat)
  requires FileExists(filename)
{
  FileSize(filename) == originalSize
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
/* code modified by LLM (iteration 5): implement proper memory mapping logic */
{
  var i := 0;
  result := [];
  
  while i < n
    invariant |result| == i
    invariant i <= n
  {
    var currentOffset := offset + i * 8;
    result := result + [ReadRealFromFile(filename, currentOffset)];
    i := i + 1;
  }
}
// </vc-code>
