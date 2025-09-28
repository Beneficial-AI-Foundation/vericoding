// <vc-preamble>
/*
 * Array creation functionality that converts sequence-like data into array format.
 * This module provides the primary array creation function that takes a list of 
 * floating-point elements and creates a vector of the same length, preserving 
 * element values and order as specified in numpy.array behavior.
 */

type Float = real

// Method to create an array from existing sequence data
// Takes a sequence of floating-point numbers and creates a vector containing exactly 
// the input data elements in the same order
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Array(data: seq<Float>) returns (result: seq<Float>)
  ensures |result| == |data|  // Result has same length as input
  ensures forall i :: 0 <= i < |data| ==> result[i] == data[i]  // All elements preserved at corresponding indices
// </vc-spec>
// <vc-code>
{
  result := data;
}
// </vc-code>
