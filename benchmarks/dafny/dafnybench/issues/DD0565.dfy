// <vc-preamble>
/*
   CS:5810 Formal Methods in Software Engineering
   Fall 2021
   The University of Iowa

   Instructor: Cesare Tinelli

   Credits: Example adapted from material by Graeme Smith
*/

/////////////////////
// Modifying arrays 
/////////////////////






// Creating new arrays  




// Initializing arrays 

method InitArray<T>(a: array<T>, d: T) 
  modifies a 
  ensures forall i :: 0 <= i < a.Length ==> a[i] == d
{ 
  var n := 0; 
  while n != a.Length 
    invariant 0 <= n <= a.Length 
    invariant forall i :: 0 <= i < n ==> a[i] == d
  {
    a[n] := d; 
    n := n + 1; 
    }
}


// Referring to prestate values of variables



// Incrementing arrays
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method IncrementArray(a: array<int>) 
  modifies a 
  ensures forall i :: 0 <= i < a.Length ==> a[i] == old(a[i]) + 1
// </vc-spec>
// <vc-code>
{
  var n := 0; 
  while n != a.Length 
    invariant 0 <= n <= a.Length 
    invariant forall i :: 0 <= i < n ==> a[i] == old(a[i]) + 1
    invariant forall i :: n <= i < a.Length ==> a[i] == old(a[i])
  { 
    a[n] := a[n] + 1; 
    n := n + 1; 
  }
}
// </vc-code>

// Copying arrays 

method CopyArray<T>(a: array<T>, b: array<T>) 
      requires a.Length == b.Length 
      modifies b 
      ensures forall i :: 0 <= i < a.Length ==> b[i] == old(a[i])
    { 
      var n := 0; 
      while n != a.Length 
        invariant 0 <= n <= a.Length 
        invariant forall i :: 0 <= i < n ==> b[i] == old(a[i]) 
        invariant forall i :: 
                    0 <= i < a.Length ==> a[i] == old(a[i]) 
      { 
      b[n] := a[n];
        n := n + 1;
      }
    }