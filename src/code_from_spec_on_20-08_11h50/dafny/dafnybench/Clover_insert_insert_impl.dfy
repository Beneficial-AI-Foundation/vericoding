method insert(line:array<char>, l:int, nl:array<char>, p:int, at:int)
  requires 0 <= l+p <= line.Length
  requires 0 <= p <= nl.Length
  requires 0 <= at <= l
  modifies line
  ensures forall i :: (0<=i<p) ==> line[at+i] == nl[i]
  ensures forall i :: (0<=i<at) ==> line[i] == old(line[i])
  ensures forall i :: (at+p<=i<l+p) ==> line[i] == old(line[i-p])
// </vc-spec>
// <vc-code>
{
  // First, shift existing characters to the right to make room
  var i := l - 1;
  while i >= at
    invariant i >= at - 1
    invariant forall j :: (0 <= j < at) ==> line[j] == old(line[j])
    invariant forall j :: (i + 1 <= j < l) ==> line[j + p] == old(line[j])
    invariant forall j :: (at <= j <= i) ==> line[j] == old(line[j])
    invariant forall j :: (l + p <= j < line.Length) ==> line[j] == old(line[j])
    decreases i - at + 1
  {
    line[i + p] := line[i];
    i := i - 1;
  }
  
  // Now copy the new characters into the gap
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
// </vc-code>