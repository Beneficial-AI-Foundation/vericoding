// <vc-preamble>
// </vc-preamble>

// <vc-helpers>

// </vc-helpers>

// <vc-spec>
method Delete(line:array<char>, l:nat, at:nat, p:nat)
  requires l <= line.Length
  requires at+p <= l
  modifies line
  ensures line[..at] == old(line[..at])
  ensures line[at..l-p] == old(line[at+p..l])
// </vc-spec>
// <vc-code>
{
  /* code modified by LLM (iteration 2): added invariant to prove that the source of the copy remains unchanged */
  var i := 0;
  while i + at < l - p
    invariant 0 <= i <= l - at - p
    invariant line[..at] == old(line[..at])
    invariant line[at .. at + i] == old(line[at + p .. at + p + i])
    invariant forall k :: at + p + i <= k < l ==> line[k] == old(line[k])
  {
    line[at+i] := line[at+p+i];
    i := i + 1;
  }
}
// </vc-code>
