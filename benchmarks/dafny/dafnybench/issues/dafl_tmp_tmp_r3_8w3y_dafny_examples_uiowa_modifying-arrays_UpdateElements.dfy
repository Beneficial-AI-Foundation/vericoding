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
// </vc-preamble>

// <vc-helpers>
// <vc-helpers>
// </vc-helpers>
// </vc-helpers>

// <vc-spec>
method UpdateElements(a: array<int>) 
  requires a.Length == 10 
  modifies a 
  ensures old(a[4]) < a[4] 
  ensures a[6] <= old(a[6]) 
  ensures a[8] == old(a[8])
// </vc-spec>
// <vc-code>
{
  a[4] := a[4] + 3; 
  a[8] := a[8] + 1; 
  a[7] := 516; 
  a[8] := a[8] - 1; 
}
// </vc-code>

// Incrementing arrays 



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