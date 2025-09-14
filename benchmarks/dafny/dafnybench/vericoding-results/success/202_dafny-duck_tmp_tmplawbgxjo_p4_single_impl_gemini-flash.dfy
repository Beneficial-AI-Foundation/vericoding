//Given two arrays of integers, it returns a single array with all integers merged. 
// [1,5,2,3],[4,3,5]->[1,5,2,3,4,3,5]

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method single(x:array<int>, y:array<int>) returns (b:array<int>) 
requires x.Length > 0
requires y.Length > 0
// ensuring that the new array is the two arrays joined
ensures b[..] == x[..] + y[..]
// </vc-spec>
// <vc-code>
{
    var new_length := x.Length + y.Length;
    var result_array := new int[new_length];
    
    // Copy elements from x to result_array
    for i := 0 to x.Length
    invariant 0 <= i <= x.Length
    invariant forall j :: 0 <= j < i ==> result_array[j] == x[j]
    {
      if i < x.Length {
        result_array[i] := x[i];
      }
    }

    // Copy elements from y to result_array, starting after x's elements
    for i := 0 to y.Length
    invariant 0 <= i <= y.Length
    invariant forall j :: 0 <= j < x.Length ==> result_array[j] == x[j]
    invariant forall j :: 0 <= j < i ==> result_array[x.Length + j] == y[j]
    {
      if i < y.Length {
        result_array[x.Length + i] := y[i];
      }
    }
    
    return result_array;
}
// </vc-code>

