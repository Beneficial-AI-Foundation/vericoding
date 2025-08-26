method Aliases(a: array<int>, b: array<int>) 
    requires a.Length >= b.Length > 100  
    modifies a
// </vc-spec>
// <vc-code>
{
  a[0] := 42;
}
// </vc-code>

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