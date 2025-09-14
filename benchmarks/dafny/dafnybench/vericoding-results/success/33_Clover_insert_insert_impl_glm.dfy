

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
  while (i >= at)
    invariant at <= i+1
    invariant i <= l-1
    invariant forall j | i+1 <= j <= l-1 :: line[j+p] == old(line[j])
    invariant forall j | at <= j <= i :: line[j] == old(line[j])
    invariant forall j | 0 <= j < at :: line[j] == old(line[j])
  {
    line[i+p] := line[i];
    i := i - 1;
  }
  
  var j := 0;
  while (j < p)
    invariant 0 <= j <= p
    invariant forall k | 0 <= k < at :: line[k] == old(line[k])
    invariant forall k | at <= k < at+j :: line[k] == nl[k - at]
    invariant forall k | at+p <= k < l+p :: line[k] == old(line[k - p])
  {
    line[at+j] := nl[j];
    j := j + 1;
  }
}
// </vc-code>

