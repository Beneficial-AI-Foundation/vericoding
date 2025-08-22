//IMPL 
method insert(line:array<char>, l:int, nl:array<char>, p:int, at:int)
  requires 0 <= l+p <= line.Length
  requires 0 <= p <= nl.Length
  requires 0 <= at <= l
  modifies line
  ensures forall i :: (0<=i<p) ==> line[at+i] == nl[i]
  ensures forall i :: (0<=i<at) ==> line[i] == old(line[i])
  ensures forall i :: (at+p<=i<l+p) ==> line[i] == old(line[i-p])
{
  /* code modified by LLM (iteration 1): Added ghost variable to track original state */
  ghost var original := line[..];
  
  // First, shift the existing characters to the right to make space
  var i := l - 1;
  while i >= at
    invariant i >= at - 1
    invariant at <= l
    /* code modified by LLM (iteration 1): Corrected invariants for proper shifting verification */
    invariant forall j :: (i+1<=j<l) ==> line[j+p] == original[j]
    invariant forall j :: (0<=j<at) ==> line[j] == original[j]
    invariant forall j :: (at<=j<=i) ==> line[j] == original[j]
    invariant forall j :: (l+p<=j<line.Length) ==> line[j] == original[j]
    decreases i - at + 1
  {
    line[i+p] := line[i];
    i := i - 1;
  }
  
  // Now insert the new characters from nl
  i := 0;
  while i < p
    invariant 0 <= i <= p
    /* code modified by LLM (iteration 1): Corrected invariants to establish all postconditions */
    invariant forall j :: (0<=j<i) ==> line[at+j] == nl[j]
    invariant forall j :: (0<=j<at) ==> line[j] == original[j]
    invariant forall j :: (at+p<=j<l+p) ==> line[j] == original[j-p]
    decreases p - i
  {
    line[at+i] := nl[i];
    i := i + 1;
  }
}