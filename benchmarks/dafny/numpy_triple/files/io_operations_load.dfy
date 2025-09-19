// <vc-preamble>
/*
 * Specification for numpy.load functionality - loading arrays from binary files.
 * 
 * This module captures the essential behavior of loading serialized array data
 * from disk storage, supporting .npy, .npz, and pickled file formats.
 * Focuses on data preservation, size consistency, and security constraints.
 */

// Predicate to model that a file exists and is readable
ghost predicate FileExists(file: string)

// Predicate to model that a file contains valid array data
ghost predicate ValidArrayFile(file: string)

// Predicate to model that a file contains object arrays requiring pickle support
ghost predicate RequiresPickle(file: string)

// Function to model the stored data in a file (for specification purposes)
ghost function StoredData(file: string): seq<real>
  requires FileExists(file) && ValidArrayFile(file)

// Function to model the stored array size in a file
ghost function StoredSize(file: string): nat
  requires FileExists(file) && ValidArrayFile(file)

// Load arrays from binary files (.npy, .npz, or pickled files)
// </vc-preamble>

// <vc-helpers>
// </vc-helpers>

// <vc-spec>
method Load(file: string, allow_pickle: bool := false) returns (result: seq<real>)
  // Preconditions: file must exist, be readable, and contain valid array data
  requires FileExists(file)
  requires ValidArrayFile(file)
  // Security constraint: if file requires pickle support, allow_pickle must be true
  requires RequiresPickle(file) ==> allow_pickle
  
  // Postconditions capturing the essential properties
  ensures |result| == StoredSize(file)  // Size consistency with stored data
  ensures result == StoredData(file)    // Data preservation and determinism
// </vc-spec>
// <vc-code>
{
  assume {:axiom} false;
}
// </vc-code>
