// <vc-preamble>
// Abstract representation of file data for specification purposes
datatype FileData = FileData(content: seq<real>, valid: bool)

/**
 * Reads data from a file into a sequence of real numbers.
 * Corresponds to numpy.fromfile functionality for numeric data.
 * 
 * @param n: Number of elements to read and return
 * @param file: File data structure containing content and validity flag  
 * @param count: Number of items to read (-1 for all, or must equal n)
 * @param offset: Starting position (in elements) within the file content
 * @returns: Sequence of n real numbers read from the file
 */
// </vc-preamble>

// <vc-helpers>
/* helper modified by LLM (iteration 2): Removed placeholder helper comment as no helpers are needed */
// </vc-helpers>

// <vc-spec>
method fromfile(n: nat, file: FileData, count: int, offset: nat) returns (result: seq<real>)
  requires file.valid == true
  requires count == n || count == -1
  requires offset <= |file.content|
  requires |file.content| - offset >= n
  ensures |result| == n
  ensures forall i :: 0 <= i < n ==> result[i] == file.content[offset + i]
  ensures n <= |file.content| - offset
// </vc-spec>
// <vc-code>
/* code modified by LLM (iteration 2): Initialized result as an array<real> and then converted to seq<real> at the end */
{
  var i := 0;
  var temp_result: array<real> := new real[n];
  while i < n
    invariant 0 <= i <= n
    invariant temp_result.Length == n
    invariant forall j :: 0 <= j < i ==> temp_result[j] == file.content[offset + j]
  {
    temp_result[i] := file.content[offset + i];
    i := i + 1;
  }
  result := temp_result[..];
}
// </vc-code>
