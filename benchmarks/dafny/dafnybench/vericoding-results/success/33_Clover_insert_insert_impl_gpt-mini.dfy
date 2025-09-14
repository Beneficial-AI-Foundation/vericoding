

// <vc-helpers>
// No helper lemmas required for this proof.
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
  var i := l - 1;
  while i >= at
    invariant at <= i+1 <= l
    invariant forall j :: i+1 <= j < l ==> line[j+p] == old(line[j])
    invariant forall j :: 0 <= j <= i ==> line[j] == old(line[j])
    invariant forall j :: 0 <= j < at ==> line[j] == old(line[j])
    decreases i - at + 1
  {
    line[i + p] := line[i];
    i := i - 1;
  }

  var k := 0;
  while k < p
    invariant 0 <= k <= p
    invariant at + k <= l + p
    invariant forall j :: 0 <= j < k ==> line[at + j] == nl[j]
    invariant forall j :: 0 <= j < at ==> line[j] == old(line[j])
    invariant forall j :: at + p <= j < l + p ==> line[j] == old(line[j - p])
    decreases p - k
  {
    line[at + k] := nl[k];
    k := k + 1;
  }
}
// </vc-code>

