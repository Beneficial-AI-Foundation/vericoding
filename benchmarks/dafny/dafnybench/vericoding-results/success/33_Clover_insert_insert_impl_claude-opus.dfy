

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
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
  // Shift existing characters to the right by p positions
  // We need to go from right to left to avoid overwriting
  var i := l - 1;
  while i >= at
    invariant at - 1 <= i < l
    invariant forall j :: (0 <= j < at) ==> line[j] == old(line[j])
    invariant forall j :: (i < j < l) ==> line[j + p] == old(line[j])
    invariant forall j :: (at <= j <= i) ==> line[j] == old(line[j])
  {
    line[i + p] := line[i];
    i := i - 1;
  }
  
  // Insert the new characters from nl
  var k := 0;
  while k < p
    invariant 0 <= k <= p
    invariant forall j :: (0 <= j < k) ==> line[at + j] == nl[j]
    invariant forall j :: (0 <= j < at) ==> line[j] == old(line[j])
    invariant forall j :: (at + p <= j < l + p) ==> line[j] == old(line[j - p])
  {
    line[at + k] := nl[k];
    k := k + 1;
  }
}
// </vc-code>

