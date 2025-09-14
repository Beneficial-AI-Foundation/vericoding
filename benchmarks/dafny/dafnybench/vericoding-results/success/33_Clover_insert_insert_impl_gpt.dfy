

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
  var i := l;
  while i > at
    invariant 0 <= at <= l
    invariant 0 <= p
    invariant l + p <= line.Length
    invariant at <= i <= l
    invariant forall j :: i + p <= j < l + p ==> line[j] == old(line[j - p])
    invariant forall j :: 0 <= j < at ==> line[j] == old(line[j])
    invariant forall j :: 0 <= j < i ==> line[j] == old(line[j])
    decreases i - at
  {
    i := i - 1;
    line[i + p] := line[i];
  }
  var k := 0;
  while k < p
    invariant 0 <= at <= l
    invariant 0 <= p
    invariant l + p <= line.Length
    invariant 0 <= k <= p
    invariant forall q :: 0 <= q < k ==> line[at + q] == nl[q]
    invariant forall j :: at + p <= j < l + p ==> line[j] == old(line[j - p])
    invariant forall j :: 0 <= j < at ==> line[j] == old(line[j])
    decreases p - k
  {
    line[at + k] := nl[k];
    k := k + 1;
  }
}
// </vc-code>

