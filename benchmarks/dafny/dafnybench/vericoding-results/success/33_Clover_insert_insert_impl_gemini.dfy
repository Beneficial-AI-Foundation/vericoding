// <vc-preamble>
// </vc-preamble>

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
  var i := l - 1;
  while i >= at
    decreases i
    invariant at <= i + 1 <= l
    invariant forall k :: 0 <= k < at ==> line[k] == old(line[k])
    invariant forall k :: at <= k <= i ==> line[k] == old(line[k])
    invariant forall k :: i + 1 <= k < l ==> line[k+p] == old(line[k])
  {
    line[i+p] := line[i];
    i := i - 1;
  }

  var j := 0;
  while j < p
    decreases p - j
    invariant 0 <= j <= p
    invariant forall k :: 0 <= k < at ==> line[k] == old(line[k])
    invariant forall k :: (at+p <= k < l+p) ==> line[k] == old(line[k-p])
    invariant forall k :: 0 <= k < j ==> line[at+k] == nl[k]
  {
    line[at+j] := nl[j];
    j := j + 1;
  }
}
// </vc-code>
