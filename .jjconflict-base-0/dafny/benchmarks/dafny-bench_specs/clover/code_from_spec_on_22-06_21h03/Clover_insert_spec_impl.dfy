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
  /* code modified by LLM (iteration 1): Fixed loop invariants to properly track shifting elements from right to left */
  // First, shift existing characters to the right to make space
  var i := l - 1;
  while i >= at
    invariant -1 <= i < l
    invariant forall j :: (0 <= j < at) ==> line[j] == old(line[j])
    invariant forall j :: (i + 1 <= j < l) ==> line[j + p] == old(line[j])
    invariant forall j :: (at <= j <= i) ==> line[j] == old(line[j])
    decreases i + 1
  {
    line[i + p] := line[i];
    i := i - 1;
  }
  
  /* code modified by LLM (iteration 1): Fixed invariants to correctly preserve shifted elements during insertion */
  // Now insert the new characters
  i := 0;
  while i < p
    invariant 0 <= i <= p
    invariant forall j :: (0 <= j < at) ==> line[j] == old(line[j])
    invariant forall j :: (0 <= j < i) ==> line[at + j] == nl[j]
    invariant forall j :: (at + p <= j < l + p) ==> line[j] == old(line[j - p])
  {
    line[at + i] := nl[i];
    i := i + 1;
  }
}